// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

module internal Clef.Compiler.UnicodeLexing

open System.IO
open Clef.Compiler.Features
open Clef.Compiler.Text
open Internal.Utilities.Text.Lexing

type Lexbuf = LexBuffer<char>

type LexBuffer<'char> with
    member GetLocalData<'T when 'T: not null> : key: string * initializer: (unit -> 'T) -> 'T
    member TryGetLocalData<'T when 'T: not null> : key: string -> 'T option

val StringAsLexbuf:
    reportLibraryOnlyFeatures: bool * langVersion: LanguageVersion * strictIndentation: bool option * string -> Lexbuf

val FunctionAsLexbuf:
    reportLibraryOnlyFeatures: bool *
    langVersion: LanguageVersion *
    strictIndentation: bool option *
    bufferFiller: (char[] * int * int -> int) ->
        Lexbuf

val SourceTextAsLexbuf:
    reportLibraryOnlyFeatures: bool *
    langVersion: LanguageVersion *
    strictIndentation: bool option *
    sourceText: ISourceText ->
        Lexbuf

/// Will not dispose of the stream reader.
val StreamReaderAsLexbuf:
    reportLibraryOnlyFeatures: bool *
    langVersion: LanguageVersion *
    strictIndentation: bool option *
    reader: StreamReader ->
        Lexbuf
