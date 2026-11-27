// Host build tool. FSI loads the tokenizer from the selected SDK.
//
// Two modes, one ratchet implementation (clef #165, ADL ZONE-A-ANALYZER-BOUNDARY):
//   check   <compile-inputs> <allowances> [--emit-scope]
//           Enforces EXACT EQUALITY of every Zone A site count against the
//           checked-in build/ClefCore.allowances.tsv. A count above its row is
//           an expansion; a count below its row is stale slack that must be
//           lowered ("lower to N") or removed ("remove row"); a row whose file
//           has zero actual sites is refused outright.
//   ratchet <base-blob> <candidate> [--admit-new-rules <base-census>]
//           Enforces shrink-only non-expansion against a git base revision blob:
//           a new file/name key or a raised count is refused, reporting every
//           mismatch rather than stopping at the first. With --admit-new-rules,
//           rules already tracked in <base-blob> remain strictly shrink-only
//           while newly introduced rules may not exceed <base-census>.
//
// Zone A bans never depend on preprocessor defines: every conditional branch of
// a Zone A file is scanned while saving and restoring lexical state across
// #if/#elif/#else/#endif and propagating branch-exit identifier chains / `open
// type` contexts across directive boundaries. Line directives (#line and
// # <int>), #light, #indent, #define, #undef, interactive # directives (#r,
// #reference, #load, #I, #time, #quit, #help), and mid-line #nowarn/#warnon
// directives are refused outright at any column in clean token state with
// CLEF001 while preserving identifier-chain and `open type` state across line
// directives and #light/#indent so trailing lines and split chains are still
// scanned. Line-start #nowarn/#warnon directives (where F# rejects trailing
// code with FS0203) act as trivia for chain / `open type` tracking; genuine
// flexible types (e.g. #IDisposable, #line_suffix) remain permitted.
//
// Any conditional branch ending in an unclosed comment, string literal, or
// interpolation hole is refused with CLEF001 and the saved state is restored so
// subsequent active code is still scanned. Conditional directives inside
// interpolated-string holes, any token reaching the tokenizer's packed nesting
// bit-width limits (comment depth >= 16, hole brace depth >= 8, nested
// interpolated string depth >= 3, extended interpolated string delimiter >= 8 `$`),
// files ending in unclosed lexical states, and any InactiveCode/HASH_IF/IfDefSkip
// state are refused with CLEF001.
//
// `%A` reflection formatting is scanned in regular, verbatim, triple-quoted,
// single-`$` interpolated (odd `%` run), and extended `$$..."""` interpolated
// (`n >= 2` `$`, `%` run length `>= n`) strings for `%[+\-0 #]*[0-9*]*(\.[0-9*]*)?A`,
// after decoding F# escape sequences in regular and regular-interpolated `$`
// strings (`%%A`/`%%%%A` in `n = 1` strings and `< n` `%` runs in `n >= 2`
// strings are literal text). Decimal trigraph escapes containing non-ASCII
// Unicode digits or values above 255 are refused outright with CLEF001 and
// also decoded with F#'s low-byte rule so any encoded `%A` is counted too.
// Textual scanning does not resolve type/module aliases, constant-folded format
// strings, `ThrowIf*`/`nullArgCheck`/`nonNull`/`ExceptionDispatchInfo.Throw`,
// `exit`, `Process.Start`, `typeof<_>.GetMethods()`, or implicit `ToString`/`%O`
// formatting (tracked for typed analyzers in #165-B).
open System
open System.Globalization
open System.IO
open FSharp.Compiler.Tokenization

type Site = { File: string; Name: string; Line: int; Column: int }

type DirectiveKind =
    | CondIf
    | CondElif
    | CondElse
    | CondEndif
    | LineDirective

type StringContext = {
    DollarCount: int
    DecodesEscapes: bool
}

type InterpFrame = {
    Context: StringContext
    HoleBraceDepth: int
}

type TokenContext = {
    Chain: (string * int * int) list
    AfterDot: bool
    ChainStartsAfterDot: bool
    PrevTok2: string option
    PrevTok1: string option
}

type SavedCondState = {
    LexState: FSharpTokenizerLexState
    CommentDepth: int
    InterpStack: InterpFrame list
    EntryContexts: TokenContext list
    BranchExits: TokenContext list
    HasElse: bool
}

let emptyTokenContext =
    { Chain = []
      AfterDot = false
      ChainStartsAfterDot = false
      PrevTok2 = None
      PrevTok1 = None }

let dedupContexts (ctxs: TokenContext list) =
    ctxs
    |> List.distinctBy (fun c ->
        (c.Chain |> List.map (fun (n, _, _) -> n),
         c.AfterDot,
         c.ChainStartsAfterDot,
         c.PrevTok2,
         c.PrevTok1))

let roots = set ["NativeTypedTree"; "PSGSaturation"; "Baker"; "Nanopass"]

// Banned CLR/host identifiers used bare in Zone A.
let names =
    set [
        "FSharpValue"; "FSharpType"; "ConditionalWeakTable"; "ProcessStartInfo";
        "ConcurrentDictionary"; "ConcurrentQueue"; "ConcurrentBag"; "ConcurrentStack";
        "ConcurrentExclusiveSchedulerPair"; "BlockingCollection";
        "ThreadLocal"; "ThreadStatic"; "ThreadStaticAttribute";
        "IsValueCreated"; "get_IsValueCreated";
        "Reflection"; "Concurrent";
        "failwith"; "failwithf"; "invalidOp"; "invalidArg"; "nullArg"; "raise"; "reraise";
        "Stopwatch"; "Console";
        "GetEnvironmentVariable"; "GetEnvironmentVariables"; "GetFolderPath"
    ]

// Banned dotted namespace chains.
let prefixes =
    set [
        "System.Reflection"; "Microsoft.FSharp.Reflection"; "System.Collections.Concurrent";
        "System.Diagnostics.Stopwatch"; "System.Environment"; "System.Console";
        "System.Threading.ThreadLocal"
    ]

// Banned chain-head identifiers immediately followed by `.` (e.g. `Environment.Exit`)
// or directly imported via `open type Environment`, avoiding false positives on
// `TypeEnvironment` or `x.Environment`.
let chainHeadPrefixes = set ["Environment"]

let normalize (path: string) = path.Replace('\\','/')
let rules = names + prefixes + chainHeadPrefixes + set ["%A"]

let inZone (path: string) =
    let slash = path.IndexOf('/')
    slash > 0 && roots.Contains(path.Substring(0, slash))

let hasDirectiveBoundary (trimmed: string) (keyword: string) =
    trimmed.StartsWith(keyword, StringComparison.Ordinal) &&
    (trimmed.Length = keyword.Length ||
     let c = trimmed[keyword.Length]
     Char.IsWhiteSpace c || c = '(' || c = '!' || c = '/')

let isUnicodeDecimalDigit (c: char) =
    Char.GetUnicodeCategory c = UnicodeCategory.DecimalDigitNumber

let isIdentChar (c: char) =
    match Char.GetUnicodeCategory c with
    | UnicodeCategory.UppercaseLetter
    | UnicodeCategory.LowercaseLetter
    | UnicodeCategory.TitlecaseLetter
    | UnicodeCategory.ModifierLetter
    | UnicodeCategory.OtherLetter
    | UnicodeCategory.LetterNumber
    | UnicodeCategory.ConnectorPunctuation
    | UnicodeCategory.NonSpacingMark
    | UnicodeCategory.SpacingCombiningMark
    | UnicodeCategory.Format
    | UnicodeCategory.DecimalDigitNumber -> true
    | _ -> c = '_' || c = '\''

let forbiddenHashDirectives =
    set [
        "light"; "indent"; "define"; "undef"
        "r"; "reference"; "load"; "I"; "time"; "quit"; "help"
    ]

// Matches F# line directives (`# [ \t]* <digit>` or `#line` followed by EOL/whitespace)
// starting at `hashIdx` (any column, per lex.fsl line-directive rule).
let isLineDirectiveAt (line: string) (hashIdx: int) =
    let len = line.Length
    if hashIdx < 0 || hashIdx >= len || line[hashIdx] <> '#' then false
    else
        let p = hashIdx + 1
        if p + 4 <= len &&
           String.Compare(line, p, "line", 0, 4, StringComparison.Ordinal) = 0 &&
           (p + 4 = len || line[p + 4] = ' ' || line[p + 4] = '\t') then
            true
        else
            let mutable k = p
            while k < len && (line[k] = ' ' || line[k] = '\t') do
                k <- k + 1
            k < len && isUnicodeDecimalDigit line[k]

let tryForbiddenHashDirectiveAt (line: string) (hashIdx: int) =
    let len = line.Length
    if hashIdx < 0 || hashIdx >= len || line[hashIdx] <> '#' then None
    else
        let startIdx = hashIdx + 1
        let mutable endIdx = startIdx
        while endIdx < len && isIdentChar line[endIdx] do
            endIdx <- endIdx + 1
        if endIdx > startIdx then
            let word = line.Substring(startIdx, endIdx - startIdx)
            if forbiddenHashDirectives.Contains word then Some word else None
        else None

let isLineStartWarnDirective (line: string) =
    let trimmed = line.TrimStart()
    (trimmed.StartsWith("#nowarn", StringComparison.Ordinal) &&
     (trimmed.Length = 7 || Char.IsWhiteSpace trimmed[7] || trimmed[7] = '"')) ||
    (trimmed.StartsWith("#warnon", StringComparison.Ordinal) &&
     (trimmed.Length = 7 || Char.IsWhiteSpace trimmed[7] || trimmed[7] = '"'))

let classifyDirective (line: string) =
    let trimmed = line.TrimStart()
    if not (trimmed.StartsWith("#", StringComparison.Ordinal)) then None
    elif hasDirectiveBoundary trimmed "#if" then Some CondIf
    elif hasDirectiveBoundary trimmed "#elif" then Some CondElif
    elif hasDirectiveBoundary trimmed "#else" then Some CondElse
    elif hasDirectiveBoundary trimmed "#endif" then Some CondEndif
    elif isLineDirectiveAt trimmed 0 then Some LineDirective
    else None

let directiveLabel = function
    | CondIf -> "#if"
    | CondElif -> "#elif"
    | CondElse -> "#else"
    | CondEndif -> "#endif"
    | LineDirective -> "#line"

// FSharpTokenizerColorState.ExtendedInterpolatedString exists on the CLR enum in
// FCS 10.0.401 but is hidden from F# static member lookup (FS0039); resolve it by
// enum name so no bare numeric literal appears in the guard.
let extendedInterpolatedStringState =
    match Enum.TryParse<FSharpTokenizerColorState>("ExtendedInterpolatedString") with
    | true, value -> Some value
    | false, _ -> None

let isCleanTokenState (state: FSharpTokenizerLexState) =
    match FSharpLineTokenizer.ColorStateOfLexState state with
    | FSharpTokenizerColorState.InitialState
    | FSharpTokenizerColorState.Token
    | FSharpTokenizerColorState.EndLineThenToken -> true
    | _ -> false

let isSkipColorState (cs: FSharpTokenizerColorState) =
    cs = FSharpTokenizerColorState.IfDefSkip ||
    cs = FSharpTokenizerColorState.EndLineThenSkip

let isInStringState (state: FSharpTokenizerLexState) =
    let cs = FSharpLineTokenizer.ColorStateOfLexState state
    match cs with
    | FSharpTokenizerColorState.String
    | FSharpTokenizerColorState.VerbatimString
    | FSharpTokenizerColorState.TripleQuoteString -> true
    | _ -> extendedInterpolatedStringState = Some cs

let describeUnclosedState (state: FSharpTokenizerLexState) (interpOpen: bool) (commentOpen: bool) =
    let cs = FSharpLineTokenizer.ColorStateOfLexState state
    if not (isCleanTokenState state) then string cs
    elif interpOpen then "InterpolatedString"
    elif commentOpen then "Comment"
    else "Token"

let endsWithOddBackslashes (s: string) =
    let mutable n = 0
    let mutable i = s.Length - 1
    while i >= 0 && s[i] = '\\' do
        n <- n + 1
        i <- i - 1
    n % 2 = 1

let countLeadingDollars (raw: string) =
    let mutable k = 0
    while k < raw.Length && raw[k] = '$' do
        k <- k + 1
    max 1 k

let isHexDigit (c: char) =
    (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')

let isAsciiDigit (c: char) = c >= '0' && c <= '9'

let hexValue (c: char) =
    if c >= '0' && c <= '9' then int c - int '0'
    elif c >= 'a' && c <= 'f' then 10 + (int c - int 'a')
    else 10 + (int c - int 'A')

// Decodes F# string escape sequences for regular (`"..."`) and regular-interpolated
// (`$"..."`) string segments while preserving the source `(Line, Column)` of each
// escape start. Verbatim (`@"..."`, `$@"..."`, `@$"..."`) and triple-quoted
// (`"""..."""`, `$"""..."""`, `$$"""..."""`) strings are never passed here.
// Per lex.fsl (`digit = '\Nd'`, `trigraph = '\\' digit digit digit`), decimal
// trigraphs containing non-ASCII Unicode digits or values above 255 are refused
// with CLEF001 and also decoded with F#'s low-byte truncation so any encoded `%A`
// is counted on the same pass.
let decodeFSharpEscapes (file: string) (errors: ResizeArray<string>) (rawChars: ResizeArray<char * int * int>) =
    let decoded = ResizeArray<char * int * int>(rawChars.Count)
    let n = rawChars.Count
    let chAt idx = let c, _, _ = rawChars[idx] in c
    let mutable i = 0
    while i < n do
        let c, ln, col = rawChars[i]
        if c <> '\\' || i + 1 >= n then
            decoded.Add(c, ln, col)
            i <- i + 1
        else
            let next = chAt (i + 1)
            match next with
            | '\\' -> decoded.Add('\\', ln, col); i <- i + 2
            | '"' -> decoded.Add('"', ln, col); i <- i + 2
            | '\'' -> decoded.Add('\'', ln, col); i <- i + 2
            | 'n' -> decoded.Add('\n', ln, col); i <- i + 2
            | 'r' -> decoded.Add('\r', ln, col); i <- i + 2
            | 't' -> decoded.Add('\t', ln, col); i <- i + 2
            | 'b' -> decoded.Add('\b', ln, col); i <- i + 2
            | 'a' -> decoded.Add('\a', ln, col); i <- i + 2
            | 'f' -> decoded.Add('\f', ln, col); i <- i + 2
            | 'v' -> decoded.Add('\v', ln, col); i <- i + 2
            | 'u' when i + 5 < n && isHexDigit (chAt (i+2)) && isHexDigit (chAt (i+3)) &&
                       isHexDigit (chAt (i+4)) && isHexDigit (chAt (i+5)) ->
                let v =
                    (hexValue (chAt (i+2)) <<< 12) ||| (hexValue (chAt (i+3)) <<< 8) |||
                    (hexValue (chAt (i+4)) <<< 4) ||| hexValue (chAt (i+5))
                decoded.Add(char v, ln, col)
                i <- i + 6
            | 'x' when i + 3 < n && isHexDigit (chAt (i+2)) && isHexDigit (chAt (i+3)) ->
                let v = (hexValue (chAt (i+2)) <<< 4) ||| hexValue (chAt (i+3))
                decoded.Add(char v, ln, col)
                i <- i + 4
            | 'U' when i + 9 < n &&
                       isHexDigit (chAt (i+2)) && isHexDigit (chAt (i+3)) &&
                       isHexDigit (chAt (i+4)) && isHexDigit (chAt (i+5)) &&
                       isHexDigit (chAt (i+6)) && isHexDigit (chAt (i+7)) &&
                       isHexDigit (chAt (i+8)) && isHexDigit (chAt (i+9)) ->
                let mutable cp = 0u
                for k in 2 .. 9 do
                    cp <- (cp <<< 4) ||| uint32 (hexValue (chAt (i + k)))
                if cp <= 0xFFFFu then
                    decoded.Add(char cp, ln, col)
                elif cp <= 0x10FFFFu then
                    for ch in Char.ConvertFromUtf32(int cp) do
                        decoded.Add(ch, ln, col)
                else
                    decoded.Add('\\', ln, col)
                i <- i + 10
            | d1 when isUnicodeDecimalDigit d1 && i + 3 < n &&
                      isUnicodeDecimalDigit (chAt (i+2)) && isUnicodeDecimalDigit (chAt (i+3)) ->
                let d2 = chAt (i+2)
                let d3 = chAt (i+3)
                let rawVal = (int d1 - int '0') * 100 + (int d2 - int '0') * 10 + (int d3 - int '0')
                let isValidAsciiByte = isAsciiDigit d1 && isAsciiDigit d2 && isAsciiDigit d3 && rawVal <= 255
                if not isValidAsciiByte then
                    errors.Add(sprintf "%s(%d,%d): error CLEF001: non-ASCII or out-of-range decimal trigraph escape in string literal is forbidden in Zone A" file ln col)
                let decodedByte = int (char rawVal) &&& 0xFF
                decoded.Add(char decodedByte, ln, col)
                i <- i + 4
            | _ ->
                decoded.Add('\\', ln, col)
                i <- i + 1
    decoded

let inputs manifest =
    let rows = File.ReadAllLines(manifest) |> Array.map (fun row -> row.Split('\t'))
    let projectDir = rows |> Array.choose (function [|"P"; p|] -> Some p | _ -> None) |> Array.exactlyOne
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
    files

// chain is the current dotted identifier run, oldest component first.
let partsOf (prefix: string) = prefix.Split('.') |> Array.toList

let chainIds (chain: (string * int * int) list) = chain |> List.map (fun (n,_,_) -> n) |> Array.ofList

let chainEndsWith (chain: (string * int * int) list) (parts: string list) =
    let ids = chainIds chain
    let p = Array.ofList parts
    ids.Length >= p.Length && Array.sub ids (ids.Length - p.Length) p.Length = p

// Scans a reassembled string-literal segment for `%A` format specifiers of the form
// `%[+\-0 #]*[0-9*]*(\.[0-9*]*)?A`.
// - Regular, verbatim, triple-quoted, and single-`$` interpolated strings (`DollarCount = 1`):
//   an even `%` run is escaped literal percents; an odd `%` run begins a specifier at its last `%`.
// - Extended `$$..."""` interpolated strings (`DollarCount = n >= 2`):
//   runs shorter than `n` are literal text; runs of length `>= n` begin a specifier at `j - n`.
let findFormatASites (file: string) (errors: ResizeArray<string>) (ctx: StringContext) (segments: ResizeArray<int * int * string>) =
    let rawChars = ResizeArray<char * int * int>()
    for (ln, col, txt) in segments do
        for idx = 0 to txt.Length - 1 do
            rawChars.Add(txt[idx], ln, col + idx)
    let chars = if ctx.DecodesEscapes then decodeFSharpEscapes file errors rawChars else rawChars
    let n = chars.Count
    let found = ResizeArray<Site>()
    let mutable i = 0
    while i < n do
        let c, _, _ = chars[i]
        if c <> '%' then
            i <- i + 1
        else
            let mutable j = i
            while j < n && (let ch, _, _ = chars[j] in ch = '%') do
                j <- j + 1
            let runLen = j - i
            let startsSpecifier, specStart =
                if ctx.DollarCount <= 1 then
                    runLen % 2 = 1, j - 1
                else
                    runLen >= ctx.DollarCount, j - ctx.DollarCount
            if not startsSpecifier then
                i <- j
            else
                let mutable k = j
                while k < n && (let ch, _, _ = chars[k] in ch = '+' || ch = '-' || ch = '0' || ch = ' ' || ch = '#') do
                    k <- k + 1
                while k < n && (let ch, _, _ = chars[k] in (ch >= '0' && ch <= '9') || ch = '*') do
                    k <- k + 1
                if k < n && (let ch, _, _ = chars[k] in ch = '.') then
                    k <- k + 1
                    while k < n && (let ch, _, _ = chars[k] in (ch >= '0' && ch <= '9') || ch = '*') do
                        k <- k + 1
                if k < n && (let ch, _, _ = chars[k] in ch = 'A') then
                    let _, ln, col = chars[specStart]
                    found.Add({ File = file; Name = "%A"; Line = ln; Column = col })
                    i <- k + 1
                else
                    i <- j
    found |> Seq.toList

let scan (file, path) =
    // No defines: Zone A bans apply to every conditional branch, with explicit
    // lexer-state stack tracking across #if/#elif/#else/#endif. Language version
    // matches Directory.Build.props (`preview`).
    let tokenizer = FSharpSourceTokenizer([], Some path, Some "preview", None)
    let mutable state = FSharpTokenizerLexState.Initial
    let mutable commentDepth = 0
    let mutable interpStack : InterpFrame list = []
    let mutable activeStringCtx : StringContext option = None
    let mutable contexts : TokenContext list = [emptyTokenContext]
    let mutable stripLeadingWs = false
    let strSegs = ResizeArray<int * int * string>()
    let mutable condStack : SavedCondState list = []
    let sites = ResizeArray<Site>()
    let seenSites = Collections.Generic.HashSet<string * int * int>()
    let errors = ResizeArray<string>()

    let addSite (s: Site) =
        if seenSites.Add((s.Name, s.Line, s.Column)) then
            sites.Add s

    let resetContextsWithToken (tokName: string) =
        contexts <-
            contexts
            |> List.map (fun c ->
                { Chain = []
                  AfterDot = false
                  ChainStartsAfterDot = false
                  PrevTok2 = c.PrevTok1
                  PrevTok1 = Some tokName })
            |> dedupContexts

    let saveCond () =
        { LexState = state
          CommentDepth = commentDepth
          InterpStack = interpStack
          EntryContexts = contexts
          BranchExits = []
          HasElse = false }

    let restoreLexical (saved: SavedCondState) (nextContexts: TokenContext list) =
        state <- saved.LexState
        commentDepth <- saved.CommentDepth
        interpStack <- saved.InterpStack
        activeStringCtx <- None
        contexts <- dedupContexts nextContexts
        stripLeadingWs <- false
        strSegs.Clear()

    let resetToCleanToken () =
        state <- FSharpLineTokenizer.LexStateOfColorState FSharpTokenizerColorState.Token
        commentDepth <- 0
        interpStack <- []
        activeStringCtx <- None
        contexts <- [emptyTokenContext]
        stripLeadingWs <- false
        strSegs.Clear()

    let checkBranchClosed (lineNo: int) (dir: DirectiveKind) (expectedInterpDepth: int) (expectedCommentDepth: int) =
        let interpIncreased = interpStack.Length > expectedInterpDepth
        let commentIncreased = commentDepth > expectedCommentDepth
        if not (isCleanTokenState state) || interpIncreased || commentIncreased then
            let desc = describeUnclosedState state interpIncreased commentIncreased
            errors.Add(sprintf "%s(%d,1): error CLEF001: conditional branch ends in unclosed %s state before %s" file lineNo desc (directiveLabel dir))

    let mutable lastLineNo = 0
    for lineNumber, original in File.ReadLines(path) |> Seq.indexed do
        let lineNo = lineNumber + 1
        lastLineNo <- lineNo
        let inTokenState = isCleanTokenState state
        let directive =
            match classifyDirective original with
            | Some LineDirective when inTokenState -> Some LineDirective
            | Some (CondIf | CondElif | CondElse | CondEndif as d) when inTokenState || not condStack.IsEmpty -> Some d
            | _ -> None

        match directive with
        | Some LineDirective ->
            // Line directives (#line / # <int>) are forbidden in Zone A and are never fed
            // to FCS (preventing filename backslash-quote string-state leaks); preserve
            // identifier-chain and `open type` state across the line.
            errors.Add(sprintf "%s(%d,1): error CLEF001: #line / # <int> line directives are forbidden in Zone A" file lineNo)
        | Some CondIf ->
            if not interpStack.IsEmpty then
                errors.Add(sprintf "%s(%d,1): error CLEF001: preprocessor directive #if is forbidden inside an interpolated string hole" file lineNo)
            if not inTokenState then
                let expectedInterp, expectedComment =
                    match condStack with
                    | s :: _ -> s.InterpStack.Length, s.CommentDepth
                    | [] -> 0, 0
                checkBranchClosed lineNo CondIf expectedInterp expectedComment
                resetToCleanToken ()
            condStack <- saveCond () :: condStack
        | Some (CondElif | CondElse as d) ->
            match condStack with
            | saved :: rest ->
                checkBranchClosed lineNo d saved.InterpStack.Length saved.CommentDepth
                let updated =
                    { saved with
                        BranchExits = dedupContexts (saved.BranchExits @ contexts)
                        HasElse = saved.HasElse || (d = CondElse) }
                condStack <- updated :: rest
                restoreLexical updated updated.EntryContexts
            | [] ->
                errors.Add(sprintf "%s(%d,1): error CLEF001: unmatched %s directive" file lineNo (directiveLabel d))
        | Some CondEndif ->
            match condStack with
            | saved :: rest ->
                checkBranchClosed lineNo CondEndif saved.InterpStack.Length saved.CommentDepth
                let joinedContexts =
                    saved.BranchExits
                    @ contexts
                    @ (if saved.HasElse then [] else saved.EntryContexts)
                condStack <- rest
                restoreLexical saved joinedContexts
            | [] ->
                errors.Add(sprintf "%s(%d,1): error CLEF001: unmatched #endif directive" file lineNo)
        | None ->
            let lexer = tokenizer.CreateLineTokenizer(original)
            let mutable reading = true
            let mutable lineSkipReported = false
            let mutable commentLimitReported = false
            let mutable interpLimitReported = false
            let mutable braceLimitReported = false
            let mutable dollarLimitReported = false
            let mutable prevCleanEndCol = 0
            let mutable skipLightIdentAt : int option = None
            while reading do
                let prevState = state
                let prevCs = FSharpLineTokenizer.ColorStateOfLexState prevState
                let token, next = lexer.ScanToken(prevState)
                state <- next
                let nextCs = FSharpLineTokenizer.ColorStateOfLexState state
                // Detect preprocessor directives silently consumed by FSharpLineTokenizer
                // in clean token state (e.g. `#light "on"` / `#indent "on"` at any column).
                if isCleanTokenState prevState then
                    let gapEnd = match token with Some t -> t.LeftColumn | None -> original.Length
                    if gapEnd > prevCleanEndCol then
                        let gap = original.Substring(prevCleanEndCol, gapEnd - prevCleanEndCol)
                        let relHash = gap.IndexOf('#')
                        if relHash >= 0 then
                            let hashCol = prevCleanEndCol + relHash
                            let label =
                                match tryForbiddenHashDirectiveAt original hashCol with
                                | Some kw -> "#" + kw
                                | None -> "#light / #indent"
                            errors.Add(sprintf "%s(%d,%d): error CLEF001: directive %s is forbidden in Zone A" file lineNo (hashCol + 1) label)
                match token with
                | None -> reading <- false
                | Some t when t.ColorClass = FSharpTokenColorKind.InactiveCode ||
                              t.TokenName = "HASH_IF" || t.TokenName = "HASH_ELIF" ||
                              t.TokenName = "HASH_ELSE" || t.TokenName = "HASH_ENDIF" ->
                    if not lineSkipReported then
                        errors.Add(sprintf "%s(%d,%d): error CLEF001: tokenizer emitted unhandled preprocessor/inactive token %s (%O)" file lineNo (t.LeftColumn + 1) t.TokenName t.ColorClass)
                        lineSkipReported <- true
                    skipLightIdentAt <- None
                    resetContextsWithToken t.TokenName
                | Some t when t.TokenName = "HASH_LIGHT" || t.TokenName = "HASH_LINE" ->
                    errors.Add(sprintf "%s(%d,%d): error CLEF001: directive %s is forbidden in Zone A" file lineNo (t.LeftColumn + 1) t.TokenName)
                    skipLightIdentAt <- None
                | Some t when t.TokenName = "WARN_DIRECTIVE" ->
                    skipLightIdentAt <- None
                    if not (isLineStartWarnDirective original) then
                        errors.Add(sprintf "%s(%d,%d): error CLEF001: mid-line #nowarn / #warnon directive is forbidden in Zone A" file lineNo (t.LeftColumn + 1))
                | Some t when t.TokenName = "HASH" && isCleanTokenState prevState ->
                    skipLightIdentAt <- None
                    if isLineDirectiveAt original t.LeftColumn then
                        // Mid-line or line-start line directive: refuse and halt line
                        // tokenization before FCS can lex `"x\"` into an unterminated
                        // string state, while preserving `contexts` for subsequent lines.
                        errors.Add(sprintf "%s(%d,%d): error CLEF001: #line / # <int> line directives are forbidden in Zone A" file lineNo (t.LeftColumn + 1))
                        state <- prevState
                        reading <- false
                    else
                        match tryForbiddenHashDirectiveAt original t.LeftColumn with
                        | Some "light" ->
                            errors.Add(sprintf "%s(%d,%d): error CLEF001: directive #light is forbidden in Zone A" file lineNo (t.LeftColumn + 1))
                            // Preserve chain / `open type` context across bare `#light` so
                            // split chains (`System #light\n.Environment.Exit 1`) are still caught.
                            skipLightIdentAt <- Some (t.LeftColumn + 1)
                        | Some kw ->
                            errors.Add(sprintf "%s(%d,%d): error CLEF001: directive #%s is forbidden in Zone A" file lineNo (t.LeftColumn + 1) kw)
                            resetContextsWithToken t.TokenName
                        | None ->
                            resetContextsWithToken t.TokenName
                | Some t when t.ColorClass = FSharpTokenColorKind.Comment ->
                    if t.TokenName = "COMMENT" then
                        let raw = original.Substring(t.LeftColumn, t.RightColumn - t.LeftColumn + 1)
                        let inBlockOrOuter =
                            prevCs = FSharpTokenizerColorState.InitialState ||
                            prevCs = FSharpTokenizerColorState.Token ||
                            prevCs = FSharpTokenizerColorState.EndLineThenToken ||
                            prevCs = FSharpTokenizerColorState.Comment
                        if inBlockOrOuter && nextCs = FSharpTokenizerColorState.Comment && raw = "(*" then
                            commentDepth <- commentDepth + 1
                        elif prevCs = FSharpTokenizerColorState.Comment &&
                             (nextCs = FSharpTokenizerColorState.Comment || isCleanTokenState state) &&
                             raw = "*)" then
                            commentDepth <- max 0 (commentDepth - 1)
                | Some t when t.TokenName = "WHITESPACE" -> ()
                | Some t when t.ColorClass = FSharpTokenColorKind.String ->
                    skipLightIdentAt <- None
                    let raw = original.Substring(t.LeftColumn, t.RightColumn - t.LeftColumn + 1)
                    let col = t.LeftColumn + 1
                    match t.TokenName with
                    | "CHAR" | "BYTEARRAY" ->
                        strSegs.Clear()
                        activeStringCtx <- None
                        stripLeadingWs <- false
                    | "STRING" | "INTERP_STRING_BEGIN_END" | "INTERP_STRING_BEGIN_PART" | "INTERP_STRING_PART" | "INTERP_STRING_END" ->
                        let ctx =
                            match activeStringCtx with
                            | Some existing -> existing
                            | None ->
                                if (t.TokenName = "INTERP_STRING_PART" || t.TokenName = "INTERP_STRING_END") && not interpStack.IsEmpty then
                                    interpStack.Head.Context
                                else
                                    let isVerbatimOrTriple =
                                        raw.StartsWith("@", StringComparison.Ordinal) ||
                                        raw.StartsWith("$@", StringComparison.Ordinal) ||
                                        raw.StartsWith("\"\"\"", StringComparison.Ordinal) ||
                                        raw.StartsWith("$\"\"\"", StringComparison.Ordinal) ||
                                        raw.StartsWith("$$", StringComparison.Ordinal)
                                    { DollarCount = countLeadingDollars raw; DecodesEscapes = not isVerbatimOrTriple }
                        if ctx.DollarCount >= 8 && not dollarLimitReported then
                            errors.Add(sprintf "%s(%d,1): error CLEF001: extended interpolated string delimiter length %d exceeds tokenizer limit (7)" file lineNo ctx.DollarCount)
                            dollarLimitReported <- true
                        if stripLeadingWs then
                            let mutable idx = 0
                            while idx < raw.Length && (raw[idx] = ' ' || raw[idx] = '\t') do idx <- idx + 1
                            if idx < raw.Length then
                                strSegs.Add(lineNo, col + idx, raw.Substring(idx))
                            stripLeadingWs <- false
                        else
                            strSegs.Add(lineNo, col, raw)
                        for s in findFormatASites file errors ctx strSegs do addSite s
                        strSegs.Clear()
                        activeStringCtx <- None
                        match t.TokenName with
                        | "INTERP_STRING_BEGIN_PART" ->
                            interpStack <- { Context = ctx; HoleBraceDepth = 0 } :: interpStack
                        | "INTERP_STRING_PART" ->
                            match interpStack with
                            | top :: rest -> interpStack <- { top with HoleBraceDepth = 0 } :: rest
                            | [] ->
                                errors.Add(sprintf "%s(%d,%d): error CLEF001: unexpected INTERP_STRING_PART with no open interpolated string" file lineNo col)
                        | "INTERP_STRING_END" ->
                            match interpStack with
                            | _ :: rest -> interpStack <- rest
                            | [] ->
                                errors.Add(sprintf "%s(%d,%d): error CLEF001: unexpected INTERP_STRING_END with no open interpolated string" file lineNo col)
                        | _ -> ()
                    | _ ->
                        if activeStringCtx.IsNone then
                            if raw.StartsWith("}", StringComparison.Ordinal) && not interpStack.IsEmpty then
                                activeStringCtx <- Some interpStack.Head.Context
                            else
                                activeStringCtx <- Some {
                                    DollarCount = countLeadingDollars raw
                                    DecodesEscapes = (nextCs = FSharpTokenizerColorState.String)
                                }
                        if stripLeadingWs then
                            let mutable idx = 0
                            while idx < raw.Length && (raw[idx] = ' ' || raw[idx] = '\t') do idx <- idx + 1
                            if idx < raw.Length then
                                strSegs.Add(lineNo, col + idx, raw.Substring(idx))
                                stripLeadingWs <- false
                        else
                            strSegs.Add(lineNo, col, raw)
                    resetContextsWithToken t.TokenName
                | Some t when t.TokenName = "DOT" ->
                    skipLightIdentAt <- None
                    for c in contexts do
                        if not c.AfterDot && not c.ChainStartsAfterDot then
                            match c.Chain with
                            | [(name, r, col)] when chainHeadPrefixes.Contains name ->
                                addSite { File = file; Name = name; Line = r; Column = col }
                            | _ -> ()
                    contexts <-
                        contexts
                        |> List.map (fun c ->
                            { c with
                                AfterDot = true
                                PrevTok2 = c.PrevTok1
                                PrevTok1 = Some t.TokenName })
                        |> dedupContexts
                | Some t when t.TokenName = "IDENT" || t.TokenName = "VERBATIM" ->
                    let raw = original.Substring(t.LeftColumn, t.RightColumn - t.LeftColumn + 1)
                    if skipLightIdentAt = Some t.LeftColumn && raw = "light" then
                        skipLightIdentAt <- None
                    else
                        skipLightIdentAt <- None
                        let name =
                            if raw.Length >= 4 && raw.StartsWith("``", StringComparison.Ordinal) && raw.EndsWith("``", StringComparison.Ordinal)
                            then raw.Substring(2, raw.Length - 4) else raw
                        let row, column = lineNo, t.LeftColumn + 1
                        let mutable matchedPrefix = false
                        let mutable matchedOpenType = false
                        let nextContexts =
                            contexts
                            |> List.map (fun c ->
                                let isOpenTypeImport = not c.AfterDot && c.PrevTok2 = Some "OPEN" && c.PrevTok1 = Some "TYPE"
                                let nextChain, nextStartsAfterDot =
                                    if c.AfterDot && not c.Chain.IsEmpty then
                                        c.Chain @ [(name, row, column)], c.ChainStartsAfterDot
                                    else
                                        [(name, row, column)], c.AfterDot
                                let completing = prefixes |> Seq.filter (fun p -> chainEndsWith nextChain (partsOf p)) |> Seq.toList
                                if not completing.IsEmpty then
                                    matchedPrefix <- true
                                    for p in completing do addSite { File = file; Name = p; Line = row; Column = column }
                                elif isOpenTypeImport && chainHeadPrefixes.Contains name then
                                    matchedOpenType <- true
                                    addSite { File = file; Name = name; Line = row; Column = column }
                                { Chain = nextChain
                                  AfterDot = false
                                  ChainStartsAfterDot = nextStartsAfterDot
                                  PrevTok2 = c.PrevTok1
                                  PrevTok1 = Some t.TokenName })
                            |> dedupContexts
                        if not matchedPrefix && not matchedOpenType && names.Contains name then
                            addSite { File = file; Name = name; Line = row; Column = column }
                        contexts <- nextContexts
                | Some t ->
                    skipLightIdentAt <- None
                    match t.TokenName, interpStack with
                    | "LBRACE", top :: rest ->
                        interpStack <- { top with HoleBraceDepth = top.HoleBraceDepth + 1 } :: rest
                    | "RBRACE", top :: rest ->
                        interpStack <- { top with HoleBraceDepth = max 0 (top.HoleBraceDepth - 1) } :: rest
                    | _ -> ()
                    resetContextsWithToken t.TokenName

                match token with
                | Some t -> prevCleanEndCol <- max prevCleanEndCol (t.RightColumn + 1)
                | None -> ()

                // Per-token nesting-limit checks: FSharpLineTokenizer.ScanToken packs
                // comment depth (mod 16), interpolation-hole brace depth (mod 8),
                // nested interpolated string depth (max 2), and extended interpolated
                // string delimiter length (max 7 `$`) on every token.
                if reading then
                    if commentDepth >= 16 && not commentLimitReported then
                        errors.Add(sprintf "%s(%d,1): error CLEF001: block comment nesting depth %d exceeds tokenizer limit (15)" file lineNo commentDepth)
                        commentLimitReported <- true
                    if interpStack.Length >= 3 && not interpLimitReported then
                        errors.Add(sprintf "%s(%d,1): error CLEF001: nested interpolated string depth %d exceeds tokenizer limit (2)" file lineNo interpStack.Length)
                        interpLimitReported <- true
                    if not braceLimitReported then
                        match interpStack |> List.tryFind (fun f -> f.HoleBraceDepth >= 8) with
                        | Some frame ->
                            errors.Add(sprintf "%s(%d,1): error CLEF001: interpolation hole brace nesting depth %d exceeds tokenizer limit (7)" file lineNo frame.HoleBraceDepth)
                            braceLimitReported <- true
                        | None -> ()
                    if not dollarLimitReported then
                        let excessDollar =
                            match activeStringCtx with
                            | Some ctx when ctx.DollarCount >= 8 -> Some ctx.DollarCount
                            | _ ->
                                interpStack
                                |> List.tryPick (fun f -> if f.Context.DollarCount >= 8 then Some f.Context.DollarCount else None)
                        match excessDollar with
                        | Some d ->
                            errors.Add(sprintf "%s(%d,1): error CLEF001: extended interpolated string delimiter length %d exceeds tokenizer limit (7)" file lineNo d)
                            dollarLimitReported <- true
                        | None -> ()

            // Redundant fail-closed check: refuse if the tokenizer persists in a
            // conditional skip state at line end.
            let endCs = FSharpLineTokenizer.ColorStateOfLexState state
            if isSkipColorState endCs then
                if not lineSkipReported then
                    errors.Add(sprintf "%s(%d,1): error CLEF001: tokenizer entered conditional skip state %O" file lineNo endCs)
                state <- FSharpLineTokenizer.LexStateOfColorState FSharpTokenizerColorState.Token

            // Preserve multiline string content across lines; handle backslash line
            // continuation in regular strings (`"...\ \n   ..."`).
            if isInStringState state then
                if endCs = FSharpTokenizerColorState.String && endsWithOddBackslashes original && strSegs.Count > 0 then
                    let lastLn, lastCol, lastTxt = strSegs[strSegs.Count - 1]
                    if lastTxt.EndsWith("\\", StringComparison.Ordinal) then
                        strSegs[strSegs.Count - 1] <- (lastLn, lastCol, lastTxt.Substring(0, lastTxt.Length - 1))
                        stripLeadingWs <- true
                else
                    stripLeadingWs <- false
                    strSegs.Add(lineNo, original.Length + 1, "\n")

    // Unconditional EOF check: refuse any file ending in an unclosed lexical state,
    // regardless of whether a conditional directive is open.
    if not (isCleanTokenState state) || not interpStack.IsEmpty || commentDepth > 0 then
        let desc = describeUnclosedState state (not interpStack.IsEmpty) (commentDepth > 0)
        errors.Add(sprintf "%s(%d,1): error CLEF001: file ends in unclosed %s state" file (max 1 lastLineNo) desc)
    if not condStack.IsEmpty then
        errors.Add(sprintf "%s(%d,1): error CLEF001: unclosed #if directive at end of file" file (max 1 lastLineNo))

    sites |> Seq.toList, errors |> Seq.toList

let allowance path =
    File.ReadLines(path) |> Seq.fold (fun rows (line: string) ->
        match line.Split('\t') with
        | [|file; name; count|] when inZone file && rules.Contains name ->
            if count.Length > 1 && count[0] = '0' then invalidOp ("Malformed allowance: " + line)
            let n = Int32.Parse(count, NumberStyles.None, CultureInfo.InvariantCulture)
            let key = file, name
            if n < 1 || Map.containsKey key rows then invalidOp ("Invalid or duplicate allowance: " + line)
            Map.add key n rows
        | _ -> invalidOp ("Malformed allowance: " + line)) Map.empty

let maximum key counts = Map.tryFind key counts |> Option.defaultValue 0

let ratchet (accepted: Map<string * string, int>) (proposed: Map<string * string, int>) (admitBaseCensus: Map<string * string, int> option) =
    let acceptedRules = accepted |> Map.keys |> Seq.map snd |> Set.ofSeq
    let mutable valid = true
    for KeyValue((file, name) as key, n) in proposed do
        match admitBaseCensus with
        | Some baseCensus when not (acceptedRules.Contains name) ->
            let limit = maximum key baseCensus
            if n > limit then
                eprintfn "%s: error CLEF001: allowance expansion for new rule %s (base-census %d, proposed %d)." file name limit n
                valid <- false
        | _ ->
            let limit = maximum key accepted
            if n > limit then
                eprintfn "%s: error CLEF001: allowance expansion for %s (accepted %d, proposed %d)." file name limit n
                valid <- false
    valid

let run args =
    match args with
    | [|"ratchet"; stable; proposed|] ->
        ratchet (allowance stable) (allowance proposed) None
    | [|"ratchet"; stable; proposed; "--admit-new-rules"; baseCensus|] ->
        ratchet (allowance stable) (allowance proposed) (Some (allowance baseCensus))
    | [|"check"; manifest; _; "--emit-scope"|]
    | [|"check"; manifest; _|] | [|"census"; manifest|] ->
        let files = inputs manifest
        let scanned = files |> Array.map scan
        let structuralErrors = scanned |> Seq.collect snd |> Seq.toList
        let groups =
            scanned |> Seq.collect fst |> Seq.groupBy (fun s -> s.File, s.Name)
            |> Seq.map (fun (key, sites) -> key, Seq.toArray sites) |> Map.ofSeq
        if args[0] = "census" then
            for err in structuralErrors do eprintfn "%s" err
            for KeyValue((file, name), sites) in groups do printfn "%s\t%s\t%d" file name sites.Length
            structuralErrors.IsEmpty
        else
            let limits = allowance args[2]
            let mutable valid = structuralErrors.IsEmpty
            for err in structuralErrors do eprintfn "%s" err
            let report file name actual limit message =
                eprintfn "%s: error CLEF001: %s actual=%d allowance=%d - %s" file name actual limit message
                valid <- false
            for KeyValue((file, name) as key, sites) in groups do
                let limit = maximum key limits
                if sites.Length > limit then
                    let site = sites[limit]
                    eprintfn "%s(%d,%d): error CLEF001: %s allowance=%d actual=%d" file site.Line site.Column name limit sites.Length
                    valid <- false
                elif sites.Length < limit then
                    report file name sites.Length limit ("lower to " + string sites.Length)
            for KeyValue((file, name) as key, limit) in limits do
                if not (Map.containsKey key groups) then
                    report file name 0 limit "remove row"
            if valid && args.Length = 4 then
                for _, path in files do printfn "%s" path
            valid
    | _ -> invalidArg "args" "check <compile-inputs> <allowances> [--emit-scope] | census <compile-inputs> | ratchet <accepted> <proposed> [--admit-new-rules <base-census>]"

try exit (if run fsi.CommandLineArgs[1..] then 0 else 1)
with e -> eprintfn "error CLEF001: %s" e.Message; exit 2
