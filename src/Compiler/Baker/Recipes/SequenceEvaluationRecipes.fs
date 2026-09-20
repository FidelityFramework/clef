// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Compositional evaluation contracts within each sequence delimiter. Static
/// discovery visits a node once per owner to construct its local contract;
/// that bookkeeping says nothing about runtime multiplicity or availability.
module Clef.Compiler.Baker.Recipes.SequenceEvaluationRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.Obligations
open Clef.Compiler.Baker.Ingredients.Suspensions
module E = Clef.Compiler.Baker.Ingredients.Evaluation

let private local (graph: SemanticGraph) owner generator (node: SemanticNode) =
    let resident id = graph.Nodes.TryFind id |> Option.exists _.IsReachable
    let pending reason related =
        [E.pending owner node.Id reason (related |> List.filter (fun id -> graph.Nodes.ContainsKey id))], []
    let values ids = ids |> List.mapi (fun slot id -> slot, id)
    let demands operands =
        operands |> List.map (fun (slot, id) -> E.operand owner node.Id slot EvaluationAccess.Value id)
    let withOperands ids build =
        if List.forall resident ids then build (values ids)
        else pending EvaluationResidual.MissingOperand ids
    let ordered ids transfer =
        withOperands ids (fun operands -> demands operands @ E.ordered owner node.Id operands transfer, ids)
    let eager ids = ordered ids EvaluationTransfer.Continue
    let formation captures =
        let origins = captures |> List.map (fun (capture: CaptureInfo) -> capture.SourceNodeId)
        let declarations = origins |> List.choose id
        if declarations.Length <> origins.Length || not (List.forall resident declarations) then
            pending EvaluationResidual.MissingOperand declarations
        else
            let edges = declarations |> List.mapi (E.capture owner node.Id)
            edges @ E.ordered owner node.Id [] EvaluationTransfer.Continue, []
    match node.Kind with
    | SemanticKind.Sequential ids | SemanticKind.TupleExpr ids
    | SemanticKind.ArrayExpr ids | SemanticKind.ListExpr ids -> eager ids
    | SemanticKind.Application (callee, args) -> eager (callee :: args)
    | SemanticKind.ClosureValue(_, environment) -> eager [environment]
    | SemanticKind.EnvironmentReference value -> eager [value]
    | SemanticKind.EnvironmentRead(environment, _) | SemanticKind.EnvironmentBorrow(environment, _) -> eager [environment]
    | SemanticKind.EnvironmentWrite(environment, _, value) -> eager [environment; value]
    | SemanticKind.EnvironmentCreate(_, initializers) ->
        let declarations = initializers |> List.map snd
        if List.forall resident declarations then
            (declarations |> List.mapi (E.capture owner node.Id)) @ E.ordered owner node.Id [] EvaluationTransfer.Continue, []
        else pending EvaluationResidual.MissingOperand declarations
    | SemanticKind.Binding _ ->
        match node.Children with
        | [] | [_] -> eager node.Children
        | _ -> pending EvaluationResidual.InvalidShape node.Children
    | SemanticKind.Intrinsic _ -> eager node.Children
    | SemanticKind.Literal _ | SemanticKind.VarRef _
    | SemanticKind.PatternBinding _ | SemanticKind.PlatformBinding _ -> eager []
    | SemanticKind.SeqExpr _ ->
        match Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments.sequenceInitializers graph node with
        | Some pairs when pairs |> List.forall (snd >> resident) ->
            (pairs |> List.map snd |> List.mapi (E.capture owner node.Id)) @ E.ordered owner node.Id [] EvaluationTransfer.Continue, []
        | _ -> pending EvaluationResidual.MissingOperand []
    | SemanticKind.Lambda (_, _, captures, _, _)
    | SemanticKind.LazyExpr (_, captures) -> formation captures
    | SemanticKind.IfThenElse (guard, thenBranch, elseBranch) ->
        let ids = [guard; thenBranch] @ Option.toList elseBranch
        withOperands ids (fun operands ->
            let link = E.flow owner node.Id operands
            let otherwise = if elseBranch.IsSome then EvaluationPort.OperandEntry 2 else EvaluationPort.Ready
            let edges =
                [link EvaluationPort.Entry (EvaluationPort.OperandEntry 0) EvaluationTransfer.Continue
                 link (EvaluationPort.OperandExit 0) (EvaluationPort.OperandEntry 1) EvaluationTransfer.WhenTrue
                 link (EvaluationPort.OperandExit 0) otherwise EvaluationTransfer.WhenFalse
                 link (EvaluationPort.OperandExit 1) EvaluationPort.Ready EvaluationTransfer.Continue
                 link EvaluationPort.Ready EvaluationPort.Exit EvaluationTransfer.Continue]
                @ (if elseBranch.IsSome then
                       [link (EvaluationPort.OperandExit 2) EvaluationPort.Ready EvaluationTransfer.Continue]
                   else [])
            demands operands @ edges, ids)
    | SemanticKind.WhileLoop (guard, body) ->
        withOperands [guard; body] (fun operands ->
            let link = E.flow owner node.Id operands
            demands operands @
                [link EvaluationPort.Entry (EvaluationPort.OperandEntry 0) EvaluationTransfer.Continue
                 link (EvaluationPort.OperandExit 0) (EvaluationPort.OperandEntry 1) EvaluationTransfer.WhenTrue
                 link (EvaluationPort.OperandExit 0) EvaluationPort.Ready EvaluationTransfer.WhenFalse
                 link (EvaluationPort.OperandExit 1) (EvaluationPort.OperandEntry 0) EvaluationTransfer.Continue
                 link EvaluationPort.Ready EvaluationPort.Exit EvaluationTransfer.Continue], [guard; body])
    | SemanticKind.Yield payload ->
        match graph.Edges |> List.filter (fun edge -> isDelimiter edge && edge.Target = node.Id) with
        | [{ Sources = [actualOwner; actualGenerator] }] when actualOwner = owner && actualGenerator = generator ->
            ordered [payload] EvaluationTransfer.Resume
        | _ -> pending EvaluationResidual.InvalidShape [payload]
    | SemanticKind.Set (target, value) ->
        match graph.Nodes.TryFind target with
        | Some { Kind = SemanticKind.VarRef _; IsReachable = true } ->
            withOperands [target; value] (fun _ ->
                [E.operand owner node.Id 0 EvaluationAccess.Storage target
                 E.operand owner node.Id 1 EvaluationAccess.Value value]
                @ E.ordered owner node.Id [1, value] EvaluationTransfer.Continue, [value])
        | None -> pending EvaluationResidual.MissingOperand [value]
        | _ -> pending EvaluationResidual.InvalidShape [target; value]
    | SemanticKind.RecordExpr (fields, copyFrom) -> eager (Option.toList copyFrom @ List.map snd fields)
    | SemanticKind.UnionCase (_, _, payload)
    | SemanticKind.DUConstruct (_, _, payload, None) -> eager (Option.toList payload)
    | SemanticKind.DUGetTag (value, _) | SemanticKind.DUEliminate (value, _, _, _)
    | SemanticKind.TupleGet (value, _) | SemanticKind.FieldGet (value, _)
    | SemanticKind.TypeAnnotation (value, _) | SemanticKind.Deref value
    | SemanticKind.LazyForce value | SemanticKind.TraitCall (_, _, value) -> eager [value]
    | SemanticKind.FieldSet (value, _, assigned) | SemanticKind.IndexGet (value, assigned) -> eager [value; assigned]
    | SemanticKind.IndexSet (value, index, assigned)
    | SemanticKind.NamedIndexedPropertySet (value, _, index, assigned) -> eager [value; index; assigned]
    | SemanticKind.InterpolatedString parts ->
        parts |> List.choose (function InterpolatedPart.ExprPart id -> Some id | _ -> None) |> eager
    | SemanticKind.Match _ | SemanticKind.CaseElimination _ -> pending EvaluationResidual.MatchSelection []
    | SemanticKind.TryWith _ | SemanticKind.TryFinally _ -> pending EvaluationResidual.ExceptionFlow []
    | SemanticKind.ForEach _ -> pending EvaluationResidual.CollectionIteration []
    | SemanticKind.ForLoop _ -> pending EvaluationResidual.CountedIteration []
    | SemanticKind.YieldBang _ -> pending EvaluationResidual.Delegation []
    | SemanticKind.DUConstruct (_, _, _, Some _)
    | SemanticKind.Upcast _ | SemanticKind.Downcast _ | SemanticKind.TypeTest _
    | SemanticKind.AddressOf _ | SemanticKind.Quote _ | SemanticKind.ObjectExpr _
    | SemanticKind.ModuleDef _ | SemanticKind.TypeDef _ | SemanticKind.MemberDef _
    | SemanticKind.Error _ | SemanticKind.Obligation _ -> pending EvaluationResidual.InvalidShape []
    | SemanticKind.ContinuationDispatch _ | SemanticKind.FrameRead _ | SemanticKind.FrameWrite _ | SemanticKind.FrameBorrow _ ->
        pending EvaluationResidual.InvalidShape []
    | SemanticKind.ContinuationStorage _ -> pending EvaluationResidual.InvalidShape []
    | SemanticKind.ContinuationAllocate _ | SemanticKind.AggregateStorage _ -> eager []
    | SemanticKind.DUInitialize (destination, _, _, payload) -> eager (destination :: Option.toList payload)

let forOwner (graph: SemanticGraph) (owner: SemanticNode) : Enrichment =
    match owner.Kind with
    | SemanticKind.SeqExpr (generator, _) ->
        match graph.Nodes.TryFind generator with
        | Some { Kind = SemanticKind.Lambda (_, body, _, _, LambdaContext.SeqGenerator); IsReachable = true }
            when graph.Nodes.TryFind body |> Option.exists _.IsReachable ->
            let rec visit seen edges = function
                | [] -> List.rev edges |> List.concat
                | id :: rest when Set.contains id seen -> visit seen edges rest
                | id :: rest ->
                    let facts, dependencies = local graph owner.Id generator graph.Nodes[id]
                    visit (Set.add id seen) (facts :: edges) (dependencies @ rest)
            { Enrichment.empty with
                NewEdges = E.root owner.Id generator body :: visit Set.empty [] [body] }
        | _ ->
            { Enrichment.empty with
                NewEdges = [E.pending owner.Id owner.Id EvaluationResidual.InvalidShape
                                (if graph.Nodes.ContainsKey generator then [generator] else [])] }
    | _ -> Enrichment.empty
