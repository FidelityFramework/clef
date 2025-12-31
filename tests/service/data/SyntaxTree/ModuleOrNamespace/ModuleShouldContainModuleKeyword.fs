
/// this file contains patches to the F# Compiler Service that have not yet made it into
/// published nuget packages.  We source-copy them here to have a consistent location for our to-be-removed extensions

module FsAutoComplete.FCSPatches

open FSharp.Native.Compiler.Syntax
open FSharp.Native.Compiler.Text
open FsAutoComplete.UntypedAstUtils
open FSharp.Native.Compiler.CodeAnalysis

module internal SynExprAppLocationsImpl =
    let a = 42
