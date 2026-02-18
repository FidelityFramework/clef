module internal Clef.Compiler.PPLexer

open Clef.Compiler.Lexhelp
open Internal.Utilities.Text.Lexing
open Clef.Compiler.PPParser

/// Rule tokenstream
val tokenstream: args: LexArgs -> lexbuf: LexBuffer<char> -> token
/// Rule rest
val rest: lexbuf: LexBuffer<char> -> token
