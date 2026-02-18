module internal Clef.Compiler.Lexer

open Clef.Compiler.Lexhelp
open Internal.Utilities.Text.Lexing
open Clef.Compiler.Parser
open Clef.Compiler.Text
open Clef.Compiler.ParseHelpers
open Clef.Compiler.LexerStore

/// Rule token
val token: args: LexArgs -> skip: bool -> lexbuf: LexBuffer<char> -> token
/// Rule ifdefSkip
val ifdefSkip: n: int -> m: range -> args: LexArgs -> skip: bool -> lexbuf: LexBuffer<char> -> token
/// Rule endline
val endline: cont: LexerEndlineContinuation -> args: LexArgs -> skip: bool -> lexbuf: LexBuffer<char> -> token
/// Rule singleQuoteString
val singleQuoteString: sargs: LexerStringArgs -> skip: bool -> lexbuf: LexBuffer<char> -> token
/// Rule verbatimString
val verbatimString: sargs: LexerStringArgs -> skip: bool -> lexbuf: LexBuffer<char> -> token
/// Rule tripleQuoteString
val tripleQuoteString: sargs: LexerStringArgs -> skip: bool -> lexbuf: LexBuffer<char> -> token
/// Rule extendedInterpolatedString
val extendedInterpolatedString: sargs: LexerStringArgs -> skip: bool -> lexbuf: LexBuffer<char> -> token
/// Rule singleLineComment
val singleLineComment: cargs: SingleLineCommentArgs -> skip: bool -> lexbuf: LexBuffer<char> -> token
/// Rule comment
val comment: cargs: BlockCommentArgs -> skip: bool -> lexbuf: LexBuffer<char> -> token
/// Rule stringInComment
val stringInComment: n: int -> m: range -> args: LexArgs -> skip: bool -> lexbuf: LexBuffer<char> -> token
/// Rule verbatimStringInComment
val verbatimStringInComment: n: int -> m: range -> args: LexArgs -> skip: bool -> lexbuf: LexBuffer<char> -> token
/// Rule tripleQuoteStringInComment
val tripleQuoteStringInComment: n: int -> m: range -> args: LexArgs -> skip: bool -> lexbuf: LexBuffer<char> -> token
/// Rule mlOnly
val mlOnly: m: range -> args: LexArgs -> skip: bool -> lexbuf: LexBuffer<char> -> token
