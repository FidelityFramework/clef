// Copyright (c) 2025-2026 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// Baker Pipeline - Intermediate output for debugging.
///
/// ModuleClassifications is now computed lazily on the PSG itself.
/// Baker's role is to provide intermediate JSON output for the -k flag.
module FSharp.Native.Compiler.Baker.Pipeline

open System.IO
open FSharp.Native.Compiler.PSG.SemanticGraph
open FSharp.Native.Compiler.Checking.Native.Infrastructure.PhaseTypes
open FSharp.Native.Compiler.Baker.ModuleInit

//-------------------------------------------------------------------------
// JSON Serialization for Intermediates
//-------------------------------------------------------------------------

let private escapeJsonString (s: string) : string =
    s.Replace("\\", "\\\\")
     .Replace("\"", "\\\"")
     .Replace("\n", "\\n")
     .Replace("\r", "\\r")
     .Replace("\t", "\\t")

let private serializeModuleClassification (pretty: bool) (m: ModuleClassificationOutput) : string =
    let indent = if pretty then "    " else ""
    let newline = if pretty then "\n" else ""
    let sep = if pretty then ",\n" else ","

    let moduleInitStr = m.ModuleInit |> List.map string |> String.concat ", "
    let definitionsStr = m.Definitions |> List.map string |> String.concat ", "
    let entryPointStr =
        match m.EntryPoint with
        | Some ep -> string ep
        | None -> "null"

    sprintf """{%s%s"moduleId": %d%s%s"name": "%s"%s%s"moduleInit": [%s]%s%s"definitions": [%s]%s%s"entryPoint": %s%s}"""
        newline indent m.ModuleId sep
        indent (escapeJsonString m.Name) sep
        indent moduleInitStr sep
        indent definitionsStr sep
        indent entryPointStr newline

let serializeModuleInitOutput (pretty: bool) (output: BakerModuleInitOutput) : string =
    let indent = if pretty then "  " else ""
    let newline = if pretty then "\n" else ""
    let sep = if pretty then ",\n" else ","

    let modulesStr =
        output.Modules
        |> List.map (serializeModuleClassification pretty)
        |> String.concat sep

    let entryPointModulesStr =
        output.EntryPointModules
        |> List.map (fun s -> sprintf "\"%s\"" (escapeJsonString s))
        |> String.concat ", "

    sprintf """{%s%s"phase": "BakerModuleInit"%s%s"timestamp": "%s"%s%s"nodeCount": %d%s%s"reachableCount": %s%s%s"entryPointCount": %d%s%s"elapsedMs": %d%s%s"totalModuleInit": %d%s%s"totalDefinitions": %d%s%s"entryPointModules": [%s]%s%s"modules": [%s%s]%s}"""
        newline indent sep
        indent (output.Summary.Timestamp.ToString("o")) sep
        indent output.Summary.NodeCount sep
        indent (output.Summary.ReachableCount |> Option.map string |> Option.defaultValue "null") sep
        indent output.Summary.EntryPointCount sep
        indent output.Summary.ElapsedMs sep
        indent output.TotalModuleInitCount sep
        indent output.TotalDefinitionsCount sep
        indent entryPointModulesStr sep
        indent modulesStr newline newline

//-------------------------------------------------------------------------
// Pipeline Entry Point
//-------------------------------------------------------------------------

/// Emit Baker intermediates to a directory (for -k flag).
let emitIntermediates (graph: SemanticGraph) (outputDir: string) (baseName: string) : unit =
    let output = runWithOutput graph
    let moduleInitPath = Path.Combine(outputDir, sprintf "%s_baker_moduleinit.json" baseName)
    let moduleInitJson = serializeModuleInitOutput true output
    File.WriteAllText(moduleInitPath, moduleInitJson)
