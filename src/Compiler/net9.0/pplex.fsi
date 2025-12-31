module internal FSharp.Native.Compiler.PPLexer

open FSharp.Native.Compiler.Lexhelp
open Internal.Utilities.Text.Lexing
open FSharp.Native.Compiler.PPParser

/// Rule tokenstream
val tokenstream: args: LexArgs -> lexbuf: LexBuffer<char> -> token
/// Rule rest
val rest: lexbuf: LexBuffer<char> -> token
