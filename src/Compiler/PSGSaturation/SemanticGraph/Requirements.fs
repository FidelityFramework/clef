// SPDX-License-Identifier: MIT
/// Read always-active source requirements and their exact ordered match
/// authority. This validates source structure; an emitter must additionally
/// retain the actual occurrence of this frontier in its traversal context.
module Clef.Compiler.PSGSaturation.SemanticGraph.Requirements

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

type Contract = {
    Site: NodeId
    Condition: NodeId
    Diagnostic: string
    Frontier: NodeId
    Continuation: NodeId
    PatternTest: NodeId option
    Participants: NodeId list
}

let private live (graph: SemanticGraph) id = graph.Nodes.TryFind id |> Option.filter _.IsReachable
let private shallow = function
    | Pattern.Const _ | Pattern.Union(_, _, None, _) | Pattern.Union(_, _, Some Pattern.Wildcard, _) -> true
    | _ -> false

// The typed transparent input below retains the checked dimension. A native
// literal carries its value/carrier category, not a second guessed dimension
// or a source width selected from its hosted storage representation.
let private applicable inputType = function
    | Pattern.Union(_, _, _, unionType) -> applySubst unionType = applySubst inputType
    | Pattern.Const constant ->
        let inputType = applySubst inputType
        match constant with
        | NativeLiteral.Int _ | NativeLiteral.UInt _ -> Types.isIntegerType inputType
        | NativeLiteral.Float _ ->
            Types.tryGetNTUKind inputType |> Option.exists (fun kind -> NTUKind.isFloatingPoint kind || NTUKind.isPosit kind)
        | NativeLiteral.Bool _ -> inputType = Types.boolType
        | NativeLiteral.Char _ -> inputType = Types.charType
        | NativeLiteral.String _ -> inputType = Types.stringType
        | NativeLiteral.Unit -> inputType = Types.unitType
        | NativeLiteral.Decimal _ -> Types.tryGetNTUKind inputType = Some NTUKind.NTUdecimal
        | NativeLiteral.ByteArray _ -> inputType = NativeType.TApp(Types.arrayTyCon, [Types.uint8Type])
        | NativeLiteral.UInt16Array _ -> inputType = NativeType.TApp(Types.arrayTyCon, [Types.uint16Type])
    | _ -> false

let tryRequirement (graph: SemanticGraph) site =
    let rows = graph.Edges |> List.filter (fun edge ->
        edge.Role = EdgeRole.MatchRequirement && List.tryHead edge.Sources = Some site)
    match live graph site, rows with
    | Some { Kind = SemanticKind.Require(condition, diagnostic); Type = ty; Children = children },
      [{ Class = EdgeClass.Provenance; Sources = actual :: predicate :: continuation :: additional; Target = frontier; Ordinal = ordinal }]
        when actual = site && predicate = condition && children = [condition]
             && applySubst ty = Types.unitType && not (System.String.IsNullOrWhiteSpace diagnostic) ->
        match live graph condition, live graph frontier, live graph continuation with
        | Some predicate, Some { Kind = SemanticKind.Sequential [required; selected]; Type = resultType; Children = frontierChildren }, Some selectedNode
            when required = site && selected = continuation && applySubst predicate.Type = Types.boolType
                 && frontierChildren = [site; continuation] && applySubst resultType = applySubst selectedNode.Type ->
            let patternTest =
                match ordinal, additional, predicate.Kind, selectedNode.Kind with
                | 1, [], _, _ -> Some None
                | 0, [input; yes; no; body; original], SemanticKind.CaseElimination(testInput, [accepted; rejected]),
                  SemanticKind.CaseElimination(selectedInput, [selected])
                    when input = testInput && input = selectedInput && accepted.Body = yes && rejected.Body = no
                         && selected.Body = body && predicate.Children = [input; yes; no] && selectedNode.Children = [input; body]
                         && shallow accepted.Pattern && selected.Pattern = accepted.Pattern && rejected.Pattern = Pattern.Wildcard
                         && [accepted; rejected; selected] |> List.forall (fun arm -> arm.Bindings.IsEmpty && arm.Guard.IsNone) ->
                    match live graph input, live graph original, live graph yes, live graph no, live graph selected.Body with
                    | Some { Kind = SemanticKind.TypeAnnotation(source, checkedType); Type = inputType; Children = [child] }, Some original,
                      Some { Kind = SemanticKind.Literal(NativeLiteral.Bool true); Type = yesType },
                      Some { Kind = SemanticKind.Literal(NativeLiteral.Bool false); Type = noType }, Some body
                        when source = original.Id && child = original.Id
                             && applySubst checkedType = applySubst inputType && applySubst original.Type = applySubst inputType
                             && applicable inputType accepted.Pattern
                             && applySubst yesType = Types.boolType && applySubst noType = Types.boolType
                             && applySubst body.Type = applySubst selectedNode.Type -> Some(Some condition)
                    | _ -> None
                | _ -> None
            patternTest |> Option.map (fun patternTest ->
                { Site = site; Condition = condition; Diagnostic = diagnostic; Frontier = frontier
                  Continuation = continuation; PatternTest = patternTest
                  Participants = frontier :: actual :: predicate.Id :: continuation :: additional })
        | _ -> None
    | _ -> None

let tryPatternRequirement (graph: SemanticGraph) selectedDecision =
    let candidates = graph.Edges |> List.choose (fun edge ->
        match edge.Class, edge.Role, edge.Ordinal, edge.Sources with
        | EdgeClass.Provenance, EdgeRole.MatchRequirement, 0, site :: _ :: selected :: _ when selected = selectedDecision -> Some site
        | _ -> None)
    match candidates with
    | [site] -> tryRequirement graph site |> Option.filter (fun contract -> contract.PatternTest.IsSome)
    | _ -> None
