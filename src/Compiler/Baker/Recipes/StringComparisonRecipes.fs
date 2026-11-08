// SPDX-License-Identifier: MIT
/// String equality is source byte traversal. A local borrow never escapes the
/// comparison and every read goes through the ordinary memory bounds owner.
module Clef.Compiler.Baker.Recipes.StringComparisonRecipes

open XParsec.Parsers
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives
open Clef.Compiler.Baker.Recipes.Decomposition
module C = Clef.Compiler.Baker.Ingredients.Continuations
module Operations = Clef.Compiler.Baker.Ingredients.NumericOperations
module Closures = Clef.Compiler.Baker.Ingredients.Closures
module CallableOrigins = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins
module FormalDemand = Clef.Compiler.Baker.Ingredients.FormalDemand
module Participants = Clef.Compiler.Baker.Ingredients.Participants
module LazyValues = Clef.Compiler.PSGSaturation.SemanticGraph.LazyValues
module ExplicitDemand = Clef.Compiler.PSGSaturation.SemanticGraph.ExplicitDemand
module CapturedStrings = Clef.Compiler.Baker.Ingredients.CapturedStrings

/// Canonical identity stops at a formal: each invocation carries its own extent.
/// Origin enumeration follows the existing complete callable-flow relation over
/// the calls that are demanded (`FormalDemand`). A call inside an actual that
/// ordinary demand omits never reaches the formal: its actual contributes no
/// origin, and the omission relations that contain it are participants in its
/// group. The occurrences reached from `source` itself are in `group`; those an
/// input reaches are in the group of its call (`Participants.ofInputs`). A call
/// whose targets the participant form cannot state is the `Error` of the whole
/// derivation, whatever the other inputs derive; `Ok None` is a source with no
/// complete static origin.
///
/// The readers this derivation consults (formal demand, captured strings, lazy
/// facts) are facts of `graph` and `flow`; one origin reader shares them across
/// every source it derives on that graph (clef #124).
let stringOrigins (graph: SemanticGraph) (flow: CallableOrigins.Resolution) =
    let inputs = lazy (FormalDemand.reader graph flow)
    let capturedString = lazy (CapturedStrings.reader graph)
    let lazyFacts = lazy (LazyValues.settle graph)
    let capturedSource = lazy (LazyValues.tryCapturedSourceReference graph)
    // Foreign declaration bodies are placeholders, never result contracts.
    let externalImplementations =
        graph.Edges |> List.choose (fun edge ->
            match edge.Role with
            | EdgeRole.BoundaryDeclaration declaration -> Some declaration.Implementation
            | _ -> None) |> Set.ofList
    let callResult id =
        match graph.Nodes.TryFind id, flow.Calls.TryFind id with
        | Some { Kind = SemanticKind.Application(callee, actuals); Children = children; Type = ty }, Some resolved
            when Types.isStringType ty && children = callee :: actuals &&
                 resolved.Complete && not resolved.Unknown && not resolved.Targets.IsEmpty &&
                 resolved.Targets |> List.forall (fun target ->
                     not (externalImplementations.Contains target.Lambda) &&
                     target.Arguments = actuals &&
                     graph.Nodes.TryFind target.Body |> Option.exists (fun body -> Types.isStringType body.Type)) ->
            Some(callee, resolved.Targets)
        | _ -> None
    let force id =
        let facts = lazyFacts.Value
        if facts.Residuals.IsEmpty then facts.Forces.TryFind id else None
    let captured id =
        capturedSource.Value id |> Option.filter (fun declaration ->
            match graph.Nodes.TryFind declaration with
            | Some { Kind = SemanticKind.Binding(_, false, _, _) | SemanticKind.PatternBinding _ } -> true
            | _ -> false)
    // A conditional descriptor retains its own identity. Both complete immutable
    // branches contribute, even for a constant guard: this is not path inference.
    let conditional id =
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.IfThenElse(guard, yes, Some no); Children = children; Type = ty }
            when Types.isStringType ty && children = [guard; yes; no] ->
            match graph.Nodes.TryFind guard, graph.Nodes.TryFind yes, graph.Nodes.TryFind no with
            | Some condition, Some left, Some right
                when Types.tryGetNTUKind condition.Type = Some NTUKind.NTUbool &&
                     Types.isStringType left.Type && Types.isStringType right.Type -> Some(guard, yes, no)
            | _ -> None
        | _ -> None
    let rec canonical seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.VarRef(_, Some binding) } -> canonical seen binding
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> canonical seen value
        | Some { Kind = SemanticKind.TypeAnnotation(value, _) } -> canonical seen value
        | Some { Kind = SemanticKind.EagerExpr value } when ExplicitDemand.operand graph id = Some value -> canonical seen value
        | Some { Kind = SemanticKind.Sequential _ } when (force id).IsSome -> Some(id, seen)
        | Some { Kind = SemanticKind.IfThenElse _ } when (conditional id).IsSome -> Some(id, seen)
        | Some { Kind = SemanticKind.LazyRead _ } -> captured id |> Option.bind (canonical seen)
        // Preserve the current invocation's read identity. The initializer
        // enumerates possible bytes; it does not replace the environment read.
        | Some { Kind = SemanticKind.EnvironmentRead _ } -> capturedString.Value id |> Option.map (fun _ -> id, seen)
        | Some { Kind = SemanticKind.Application _ } when (callResult id).IsSome -> Some(id, seen)
        | Some { Kind = SemanticKind.Literal(NativeLiteral.String _) }
        | Some { Kind = SemanticKind.PatternBinding _ } -> Some(id, seen)
        | _ -> None
    let rec origins seen group id : Result<(Map<NodeId, bigint> * Participant list) option, Participants.TargetFailure> =
        if Set.contains id seen then Ok None else
        let seen = Set.add id seen
        let path = Result.map (Option.map (fun (values, participants) -> values, Participants.occurrence id ParticipantRole.Path 0 group :: participants))
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.Literal(NativeLiteral.String text) } ->
            Ok (Some(Map.ofList [id, bigint (System.Text.Encoding.UTF8.GetByteCount text)], [Participants.occurrence id ParticipantRole.Origin 0 group]))
        | Some { Kind = SemanticKind.VarRef(_, Some binding) } -> origins seen group binding |> path
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] }
        | Some { Kind = SemanticKind.TypeAnnotation(value, _) } -> origins seen group value |> path
        | Some { Kind = SemanticKind.EagerExpr value } when ExplicitDemand.operand graph id = Some value -> origins seen group value |> path
        | Some { Kind = SemanticKind.IfThenElse _ } ->
            match conditional id with
            | Some(guard, yes, no) ->
                match origins seen yes yes, origins seen no no with
                | Error failure, _ | _, Error failure -> Error failure
                | Ok (Some(left, leftParticipants)), Ok (Some(right, rightParticipants))
                    when not left.IsEmpty && not right.IsEmpty ->
                    let values = Map.fold (fun values origin length -> Map.add origin length values) left right
                    let joint = [id; guard; yes; no] |> List.mapi (fun ordinal node ->
                        Participants.occurrence node ParticipantRole.Construction ordinal id)
                    Ok (Some(values, joint @ leftParticipants @ rightParticipants)) |> path
                | _ -> Ok None
            | None -> Ok None
        | Some { Kind = SemanticKind.Sequential _ } when not lazyFacts.Value.Residuals.IsEmpty -> Ok None
        | Some { Kind = SemanticKind.Sequential values } ->
            match force id with
            | Some protocol ->
                let contract = lazyFacts.Value.Instances[protocol.Formation]
                let protocolNodes =
                    [ protocol.Site; protocol.Operand; protocol.Formation; protocol.EnvironmentBinding
                      protocol.Condition; protocol.CachedRead; protocol.Invocation; protocol.ResultBinding
                      protocol.ResultStore; protocol.Publication; protocol.UncachedBranch; protocol.Conditional
                      contract.Thunk; contract.ThunkBody; contract.Environment; contract.Formal
                      contract.Computed; contract.Cached; contract.InitialComputed ]
                origins seen protocol.Invocation contract.ThunkBody
                |> Result.map (Option.map (fun (values, participants) ->
                    let marker = Participants.occurrence id ParticipantRole.LazyStringOrigin 0 group
                    let protocolParticipants = protocolNodes |> List.mapi (fun ordinal node ->
                        Participants.occurrence node ParticipantRole.Construction ordinal protocol.Site)
                    values, marker :: (protocolParticipants @ participants)))
                |> path
            | None ->
                // Only the result expression contributes bytes. A damaged force
                // still ends in its conditional/cache read, neither admitted here.
                List.tryLast values |> Option.map (origins seen group) |> Option.defaultValue (Ok None) |> path
        | Some { Kind = SemanticKind.LazyRead _ } ->
            if not lazyFacts.Value.Residuals.IsEmpty then Ok None else
            captured id |> Option.map (origins seen group) |> Option.defaultValue (Ok None)
            |> Result.map (Option.map (fun (values, participants) ->
                values, Participants.occurrence id ParticipantRole.LazyStringOrigin 0 group :: participants))
            |> path
        | Some { Kind = SemanticKind.EnvironmentRead _ } ->
            match capturedString.Value id with
            | Some capture ->
                origins seen capture.Constructor capture.Initializer
                |> Result.map (Option.map (fun (values, participants) ->
                    let marker = Participants.occurrence id ParticipantRole.CapturedStringOrigin 0 group
                    let support = capture.Support |> List.mapi (fun ordinal node ->
                        Participants.occurrence node ParticipantRole.Construction ordinal id)
                    values, marker :: (support @ participants)))
                |> path
            | None -> Ok None
        | Some { Kind = SemanticKind.PatternBinding _ } ->
            match inputs.Value id with
            | Some formal ->
                (formal.Demanded |> List.map (fun input -> input, origins seen input.Call input.Actual))
                @ (formal.Omitted |> List.map (fun omitted -> omitted.Input, Ok (Some(Map.empty, []))))
                |> List.fold (fun state (input, contribution) ->
                    match state, contribution, flow.Calls.TryFind input.Call with
                    | Error failure, _, _ | _, Error failure, _ -> Error failure
                    | Ok state, Ok contribution, Some resolved when resolved.Complete && not resolved.Unknown ->
                        Participants.ofTargets input.Call resolved.Targets |> Result.map (fun targets ->
                            match state, contribution with
                            | Some(values, participants), Some(more, dependencies) ->
                                Some(Map.fold (fun acc key value -> Map.add key value acc) values more, participants @ dependencies @ targets)
                            | _ -> None)
                    | Ok _, Ok _, _ -> Ok None) (Ok (Some(Map.empty, [Participants.occurrence id ParticipantRole.Formal 0 group])))
                |> Result.map (Option.map (fun (values, participants) -> values, participants @ Participants.ofInputs id formal))
            | _ -> Ok None
        | Some { Kind = SemanticKind.Application _ } ->
            match callResult id with
            | Some(callee, targets) ->
                Participants.ofTargets id targets |> Result.bind (fun targetParticipants ->
                    targets |> List.fold (fun state target ->
                        match state, origins seen target.Lambda target.Body with
                        | Error failure, _ | _, Error failure -> Error failure
                        | Ok(Some(values, participants)), Ok(Some(more, dependencies)) when not more.IsEmpty ->
                            Ok(Some(Map.fold (fun acc key value -> Map.add key value acc) values more, participants @ dependencies))
                        | _ -> Ok None)
                        (Ok(Some(Map.empty, Participants.occurrence callee ParticipantRole.Path 0 id :: targetParticipants))))
                |> path
            | None -> Ok None
        | _ -> Ok None
    fun (group: NodeId) source ->
        origins Set.empty group source |> Result.map (fun derived ->
            match canonical Set.empty source, derived with
            | Some(identity, _), Some(values, participants) -> Some(identity, values, participants)
            | _ -> None)

/// The origins of one source in `group` (`stringOrigins`).
let stringOrigin (graph: SemanticGraph) (flow: CallableOrigins.Resolution) (group: NodeId) source =
    stringOrigins graph flow group source

/// The located error of a string at `site` whose origins are reached through a call
/// whose targets the participant form cannot state: the site, the nodes the failure
/// names, and the text that names each of them with its range.
let originError (graph: SemanticGraph) site (failure: Participants.TargetFailure) =
    let range id =
        graph.Nodes.TryFind id
        |> Option.map (fun node -> Clef.Compiler.Baker.Ingredients.Obligations.fmtRange node.Range)
        |> Option.defaultValue (sprintf "node %d, which the graph does not hold" (NodeId.value id))
    let text =
        match failure with
        | Participants.TargetFailure.UnequalCounts(call, target, arguments, parameters) ->
            sprintf "The string's origins are reached through the call at %s, whose target at %s has %d arguments and %d parameters; the participant form states one parameter for each argument of an exact invocation."
                (range call) (range target) arguments parameters
        | Participants.TargetFailure.DifferentLists call ->
            sprintf "The string's origins are reached through the call at %s, whose targets have different argument or parameter lists; the participant form states one argument list and one parameter list for a call."
                (range call)
    site, Set.ofList (site :: Participants.failureNodes failure), text

let private owned (node: SemanticNode) = node.Metadata.TryFind "Baker.StringComparisonOwned" = Some(MetadataValue.Bool true)

type private ZeroEvidenceReader = { Read: NodeId -> NodeId -> Result<Set<NodeId> option, Participants.TargetFailure> }

/// The participants of both operands when every origin of each has length zero, `Ok None`
/// otherwise, and the first failure of either operand's derivation. One reader serves
/// every comparison of one graph with one origin reader (clef #124).
let private zeroEvidenceReader (graph: SemanticGraph) =
    let origin = stringOrigins graph (CallableOrigins.resolve graph)
    let operand source =
        origin source source |> Result.map (Option.bind (fun (_,origins,participants) ->
            if not origins.IsEmpty && origins.Values |> Seq.forall ((=) 0I) then
                // Both extent rows retain any lazy/captured origin marker. It activates the
                // complete joint node/relation/root premise at source settlement.
                participants |> Participants.nodes |> Set.ofList |> Some
            else None))
    { Read = fun left right ->
        [left;right] |> List.map operand
        |> List.fold (fun state fact ->
            match state, fact with
            | Error failure, _ | _, Error failure -> Error failure
            | Ok facts, Ok fact -> Ok (Option.toList fact @ facts)) (Ok [])
        |> Result.map (function [] -> None | facts -> Some(Set.unionMany facts)) }

let private zeroEvidenceReaders = System.Runtime.CompilerServices.ConditionalWeakTable<SemanticGraph, ZeroEvidenceReader>()
let private zeroEvidenceRead =
    System.Runtime.CompilerServices.ConditionalWeakTable<SemanticGraph, ZeroEvidenceReader>.CreateValueCallback(fun graph -> zeroEvidenceReader graph)

let private zeroEvidence (graph: SemanticGraph) left right =
    (zeroEvidenceReaders.GetValue(graph, zeroEvidenceRead)).Read left right

/// The zero-extent evidence a comparison of `graph` is materialized under: a failure
/// of either operand's origins gives no evidence (see `materializeWith`).
let lengthEvidence (graph: SemanticGraph) (_: SemanticNode, _: NumericOperationKind, _: NodeId, left, right) =
    match zeroEvidence graph left right with Ok evidence -> evidence | Error _ -> None

let lengthRow site negated sources =
    { Class=EdgeClass.Provenance; Role=EdgeRole.StringLengthComparison negated; Ordinal=0; Sources=sources; Target=site }

type LengthConstruction = {
    Site: NodeId; Negated: bool; Callee: NodeId; Left: NodeId; Right: NodeId
    LeftBinding: NodeId; RightBinding: NodeId; LeftSource: NodeId; RightSource: NodeId
    LeftLength: NodeId; RightLength: NodeId; Test: NodeId; Decision: NodeId; Evidence: NodeId list
}

let lengthConstructions (graph: SemanticGraph) =
    graph.Edges |> List.choose (fun edge ->
        match edge.Class,edge.Role,edge.Ordinal,edge.Sources with
        | EdgeClass.Provenance,EdgeRole.StringLengthComparison negated,0,callee::left::right::lb::rb::ls::rs::ll::rl::test::decision::evidence ->
            Some { Site=edge.Target; Negated=negated; Callee=callee; Left=left; Right=right
                   LeftBinding=lb; RightBinding=rb; LeftSource=ls; RightSource=rs; LeftLength=ll; RightLength=rl
                   Test=test; Decision=decision; Evidence=evidence }
        | _ -> None)

type Construction = {
    Site: NodeId; Negated: bool; Callee: NodeId; Left: NodeId; Right: NodeId
    LeftBinding: NodeId; RightBinding: NodeId; LeftSource: NodeId; RightSource: NodeId
    LeftView: NodeId; RightView: NodeId; LeftLength: NodeId; RightLength: NodeId
    LengthTest: NodeId; Index: NodeId; Equal: NodeId; Guard: NodeId; Current: NodeId
    LeftRead: NodeId; RightRead: NodeId; ByteTest: NodeId; Advance: NodeId; Stop: NodeId
    Body: NodeId; Loop: NodeId; Result: NodeId; Decision: NodeId; Members: NodeId list
}

let row site negated sources =
    { Class = EdgeClass.Provenance; Role = EdgeRole.StringComparisonConstruction negated; Ordinal = 0; Sources = sources; Target = site }

let constructions (graph: SemanticGraph) =
    graph.Edges |> List.choose (fun edge ->
        match edge.Class, edge.Role, edge.Ordinal, edge.Sources with
        | EdgeClass.Provenance, EdgeRole.StringComparisonConstruction negated, 0,
          callee::left::right::lb::rb::ls::rs::lv::rv::ll::rl::lengthTest::index::equal::guard::current::lr::rr::byteTest::advance::stop::body::loop::result::decision::members ->
            Some { Site=edge.Target; Negated=negated; Callee=callee; Left=left; Right=right; LeftBinding=lb; RightBinding=rb
                   LeftSource=ls; RightSource=rs; LeftView=lv; RightView=rv; LeftLength=ll; RightLength=rl
                   LengthTest=lengthTest; Index=index; Equal=equal; Guard=guard; Current=current
                   LeftRead=lr; RightRead=rr; ByteTest=byteTest; Advance=advance; Stop=stop
                   Body=body; Loop=loop; Result=result; Decision=decision; Members=members }
        | _ -> None)

let candidates (graph: SemanticGraph) =
    graph.Nodes.Values |> Seq.choose (fun node ->
        if not node.IsReachable then None else
        match Operations.operation graph node with
        | Some(callee, kind, [left;right], _) when (kind = NumericOperationKind.Equal || kind = NumericOperationKind.NotEqual)
                                                     && Types.isStringType graph.Nodes[left].Type && Types.isStringType graph.Nodes[right].Type ->
            Some(node, kind, callee, left, right)
        | _ -> None) |> Seq.toList

/// Materialize one comparison of `graph` under the zero-extent evidence `empty`
/// (`lengthEvidence graph` of the same comparison). A failure of either operand's
/// origins gives no evidence of zero extents, so the comparison takes the byte
/// traversal, which claims nothing of the origins. Its two views derive the same
/// origins, and the borrow owner reports the failure at each view
/// (BoundaryRecipes.intrinsicWrites).
let materializeWith (empty: Set<NodeId> option) (graph: SemanticGraph) (source: SemanticNode, kind, callee, left, right) =
    let state = SaturationState.create source.Range "String.equality" (Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration.freshId()) source.Id graph.Platform
    let arrayType = Types.mkArrayType Types.intType
    let length input = saturation {
        let info = { Module=IntrinsicModule.String; Operation="length"; Category=IntrinsicCategory.Pure; FullName="String.length" }
        let! fn = createWithChildren (SemanticKind.Intrinsic info) (NativeType.TFun(Types.stringType,Types.intType)) []
        return! app fn [input] Types.intType }
    let fullParser = saturation {
        let! lb = letBind "__equal_left" left Types.stringType
        let! rb = letBind "__equal_right" right Types.stringType
        let! ls = varRef "__equal_left" (Some lb) Types.stringType
        let! rs = varRef "__equal_right" (Some rb) Types.stringType
        let! ll = length ls
        let! rl = length rs
        let! lengthTest = compareEq ll rl Types.intType
        let! lv = createWithChildren (SemanticKind.StringByteBorrow ls) arrayType [ls]
        let! rv = createWithChildren (SemanticKind.StringByteBorrow rs) arrayType [rs]
        let! zero = intLit 0
        let! yes = boolLit true
        let! index = C.mutableBinding "__equal_index" zero Types.intType
        let! equal = C.mutableBinding "__equal_result" yes Types.boolType
        let! guardIndex = varRef "__equal_index" (Some index) Types.intType
        let! guard = lt guardIndex ll Types.intType
        let! current = varRef "__equal_index" (Some index) Types.intType
        let! lr = createWithChildren (SemanticKind.IndexGet(lv,current)) Types.intType [lv;current]
        let! rr = createWithChildren (SemanticKind.IndexGet(rv,current)) Types.intType [rv;current]
        let! byteTest = compareEq lr rr Types.intType
        let! one = intLit 1
        let! next = add current one Types.intType
        let! advance = C.assign index "__equal_index" Types.intType next
        let! mismatchFalse = boolLit false
        let! markFalse = C.assign equal "__equal_result" Types.boolType mismatchFalse
        let! stopIndex = C.assign index "__equal_index" Types.intType ll
        let! stop = C.block [markFalse;stopIndex] Types.unitType
        let! body = ifThenElse byteTest advance stop Types.unitType
        let! loop = createWithChildren (SemanticKind.WhileLoop(guard,body)) Types.unitType [guard;body]
        let! result = varRef "__equal_result" (Some equal) Types.boolType
        let! traverse = evaluateBefore [index;equal;loop] result Types.boolType
        let! unequalLengthFalse = boolLit false
        let! same = ifThenElse lengthTest traverse unequalLengthFalse Types.boolType
        let! decision = if kind = NumericOperationKind.NotEqual then not' same else preturn same
        do! Closures.enrich source (SemanticKind.Sequential [lb;rb;decision]) Types.boolType [lb;rb;decision] source.EmissionStrategy false
        return [callee;left;right;lb;rb;ls;rs;lv;rv;ll;rl;lengthTest;index;equal;guard;current;lr;rr;byteTest;advance;stop;body;loop;result;decision]
      }
    let parser =
        match empty with
        | None -> fullParser
        | Some evidence -> saturation {
            let! lb = letBind "__equal_left" left Types.stringType
            let! rb = letBind "__equal_right" right Types.stringType
            let! ls = varRef "__equal_left" (Some lb) Types.stringType
            let! rs = varRef "__equal_right" (Some rb) Types.stringType
            let! ll = length ls
            let! rl = length rs
            let! test = compareEq ll rl Types.intType
            let! decision = if kind=NumericOperationKind.NotEqual then not' test else preturn test
            do! Closures.enrich source (SemanticKind.Sequential [lb;rb;decision]) Types.boolType [lb;rb;decision] source.EmissionStrategy false
            return [callee;left;right;lb;rb;ls;rs;ll;rl;test;decision] @ Set.toList evidence
          }
    match run state parser with
    | NoMatch reason, _ -> invalidOp ("String comparison construction failed: " + reason)
    | Matched roles, nodes ->
        let nodes = nodes |> List.map (fun node ->
            let metadata = node.Metadata.Add("Baker.StringComparisonOwned",MetadataValue.Bool true)
            let metadata = if empty.IsSome && node.Id=source.Id then metadata.Add("Baker.StringLengthComparison",MetadataValue.Bool true) else metadata
            { node with Metadata=metadata })
        let old = Closures.structuralIncidence source
        let key (edge: Hyperedge) = edge.Class,edge.Role,edge.Ordinal,edge.Sources,edge.Target
        let removed = old |> List.map key |> Set.ofList
        let construction = if empty.IsSome then lengthRow source.Id (kind=NumericOperationKind.NotEqual) roles
                           else row source.Id (kind=NumericOperationKind.NotEqual) (roles @ (nodes |> List.map _.Id))
        let edges = (graph.Edges |> List.filter (fun edge -> not(removed.Contains(key edge))))
                    @ (nodes |> List.collect Closures.structuralIncidence)
                    @ [construction]
        mkResultNoShadow nodes source.Id [], edges

let materialize (graph: SemanticGraph) candidate =
    materializeWith (lengthEvidence graph candidate) graph candidate

let private calleeMatches graph negated callee =
    match BoundaryDeclarations.target graph callee with
    | Some({ Kind=SemanticKind.Intrinsic { Module=IntrinsicModule.Operators; Operation=operation } },_) ->
        operation=(if negated then "op_Inequality" else "op_Equality")
    | _ -> false

let private lengthStructure (graph: SemanticGraph) (c: LengthConstruction) =
    let kind id = graph.Nodes.TryFind id |> Option.map _.Kind
    let binding actual id = match graph.Nodes.TryFind id with Some { Kind=SemanticKind.Binding(_,false,_,_); Children=[value] } -> value=actual | _ -> false
    let reference binding id = match kind id with Some(SemanticKind.VarRef(_,Some actual)) -> actual=binding | _ -> false
    let length source id = match kind id with
                           | Some(SemanticKind.Application(fn,[actual])) when actual=source ->
                               match kind fn with Some(SemanticKind.Intrinsic { Module=IntrinsicModule.String; Operation="length" }) -> true | _ -> false
                           | _ -> false
    let test = graph.Nodes.TryFind c.Test |> Option.bind (Operations.operation graph) |> Option.exists (fun (_,kind,args,_) -> kind=NumericOperationKind.Equal && args=[c.LeftLength;c.RightLength])
    let decision =
        if not c.Negated then c.Decision=c.Test else
        match kind c.Decision with
        | Some(SemanticKind.IfThenElse(test,yes,Some no)) ->
            test=c.Test && kind yes=Some(SemanticKind.Literal(NativeLiteral.Bool false)) && kind no=Some(SemanticKind.Literal(NativeLiteral.Bool true))
        | _ -> false
    calleeMatches graph c.Negated c.Callee && kind c.Site=Some(SemanticKind.Sequential [c.LeftBinding;c.RightBinding;c.Decision]) &&
    binding c.Left c.LeftBinding && binding c.Right c.RightBinding && reference c.LeftBinding c.LeftSource && reference c.RightBinding c.RightSource &&
    length c.LeftSource c.LeftLength && length c.RightSource c.RightLength && test && decision

/// Whether the construction still has its source structure and its zero-extent
/// evidence, or the failure of the origins that evidence is derived from.
let validLengthStructure (graph: SemanticGraph) (c: LengthConstruction) =
    zeroEvidence graph c.Left c.Right |> Result.map (fun evidence ->
        lengthStructure graph c && evidence=Some(Set.ofList c.Evidence))

/// Complete only this recipe's just-folded rewrite, after ordinary demand is
/// current. The operand bindings add structural scope participants. Retain every
/// earlier premise and the exact construction prefix; never repair an arbitrary
/// late/stale row. A failed derivation keeps the original row so the existing
/// owning validation reports the same located failure (including origin errors).
let settleMaterializedLength (before: SemanticGraph) (current: SemanticGraph)
    (source: SemanticNode, operation, callee, left, right) =
    let own (edge: Hyperedge) =
        edge.Target=source.Id &&
        (match edge.Role with EdgeRole.StringLengthComparison _ -> true | _ -> false)
    let rows = current.Edges |> List.filter own
    let facts = lengthConstructions current |> List.filter (fun fact -> fact.Site=source.Id)
    match rows, facts with
    | [row], [fact] when fact.Callee=callee && fact.Left=left && fact.Right=right &&
                        fact.Negated=(operation=NumericOperationKind.NotEqual) && lengthStructure current fact ->
        match zeroEvidence before left right, zeroEvidence current left right with
        | Result.Ok(Some early), Result.Ok(Some settled)
            when early=Set.ofList fact.Evidence && Set.isSubset early settled ->
            let sources = (row.Sources |> List.take 11) @ Set.toList settled
            let replacement = { row with Sources=sources }
            let edges = current.Edges |> List.map (fun edge -> if own edge then replacement else edge)
            { current with Edges=edges }
        | _ -> current
    | _ -> current

/// Transfer only already-valid length constructions across the factory result
/// destination rewrite. That owner replaces a source call by an ordered storage
/// prefix and a new invocation, so current call/formal premises replace the old
/// ones. The exact construction row must itself be untouched. Both source
/// graphs are checked; this is not a late stale-proof refresh for publication.
let transferLengthAfterFactoryRewrite (before: SemanticGraph) (current: SemanticGraph) =
    let own (edge: Hyperedge) =
        match edge.Role with EdgeRole.StringLengthComparison _ -> true | _ -> false
    let rows (graph: SemanticGraph) site =
        graph.Edges |> List.filter (fun edge -> edge.Target=site && own edge)
    let key (edge: Hyperedge) = edge.Class,edge.Role,edge.Ordinal,edge.Target,edge.Sources
    let replacements =
        lengthConstructions before |> List.choose (fun fact ->
            match rows before fact.Site, rows current fact.Site with
            | [oldRow], [newRow] when key oldRow=key newRow ->
                match validLengthStructure before fact with
                | Result.Ok true when lengthStructure current fact ->
                    match zeroEvidence current fact.Left fact.Right with
                    | Result.Ok(Some settled) ->
                        let sources = (newRow.Sources |> List.take 11) @ Set.toList settled
                        Some(fact.Site, { newRow with Sources=sources })
                    | _ -> None
                | _ -> None
            | _ -> None)
        |> Map.ofList
    if replacements.IsEmpty then current else
    let edges = current.Edges |> List.map (fun edge ->
        match replacements.TryFind edge.Target with
        | Some replacement when own edge -> replacement
        | _ -> edge)
    // Preserve failed rows so the existing owner reports their exact source
    // failure. Existing factory rewrite nodes, incidence and metadata remain.
    { current with Edges=edges }

/// Identity and lifetime of this view are the containing comparison's actual
/// string value, independently of where that string's backing bytes were made.
let localView (graph: SemanticGraph) view =
    constructions graph |> List.choose (fun construction ->
        let pair = if view=construction.LeftView then Some(construction.LeftSource,construction.LeftLength)
                   elif view=construction.RightView then Some(construction.RightSource,construction.RightLength) else None
        pair |> Option.bind (fun (source,length) ->
            if construction.Members |> List.forall (fun id -> graph.Nodes.TryFind id |> Option.exists owned) then
                Some(source,length,Set.ofList(construction.Site::construction.Callee::construction.Left::construction.Right::construction.Members))
            else None)) |> function [one] -> Some one | _ -> None

/// Recheck construction correspondence at the source owner after subsequent
/// source rewrites. Publication retains its complete relation without replay.
let validStructure (graph: SemanticGraph) (c: Construction) =
    let kind id = graph.Nodes.TryFind id |> Option.map _.Kind
    let refTo binding id = match kind id with Some(SemanticKind.VarRef(_,Some actual)) -> actual=binding | _ -> false
    let literal value id = kind id = Some(SemanticKind.Literal value)
    let bool value id = literal (NativeLiteral.Bool value) id
    let integer value id = match kind id with Some(SemanticKind.Literal(NativeLiteral.Int(actual,_))) -> actual=value | _ -> false
    let op expected actuals id =
        graph.Nodes.TryFind id |> Option.bind (Operations.operation graph)
        |> Option.exists (fun (_,operation,operands,_) -> operation=expected && operands=actuals)
    let binding mutable' actual id =
        match graph.Nodes.TryFind id with
        | Some { Kind=SemanticKind.Binding(_,isMutable,_,_); Children=[value] } -> isMutable=mutable' && actual value
        | _ -> false
    let set binding value id = match kind id with Some(SemanticKind.Set(target,actual)) -> refTo binding target && value actual | _ -> false
    let length source id =
        match kind id with
        | Some(SemanticKind.Application(fn,[actual])) when actual=source ->
            match kind fn with Some(SemanticKind.Intrinsic { Module=IntrinsicModule.String; Operation="length" }) -> true | _ -> false
        | _ -> false
    let same =
        if not c.Negated then Some c.Decision else
        match kind c.Decision with Some(SemanticKind.IfThenElse(test,yes,Some no)) when bool false yes && bool true no -> Some test | _ -> None
    let decision = same |> Option.exists (fun same ->
        match kind same with
        | Some(SemanticKind.IfThenElse(test,traverse,Some no)) when test=c.LengthTest && bool false no ->
            kind traverse=Some(SemanticKind.Sequential [c.Index;c.Equal;c.Loop;c.Result])
        | _ -> false)
    let advance = set c.Index (fun next ->
        graph.Nodes.TryFind next |> Option.bind (Operations.operation graph)
        |> Option.exists (fun (_,operation,operands,_) ->
            match operation,operands with NumericOperationKind.Add,[current;one] -> current=c.Current && integer 1L one | _ -> false)) c.Advance
    let stop = match kind c.Stop with
               | Some(SemanticKind.Sequential [mark;finish]) -> set c.Equal (bool false) mark && set c.Index ((=) c.LeftLength) finish
               | _ -> false
    let branchValuesDistinct =
        match same |> Option.bind kind,kind c.Stop with
        | Some(SemanticKind.IfThenElse(_,_,Some unequalLength)),Some(SemanticKind.Sequential(mark::_)) ->
            match kind mark with Some(SemanticKind.Set(_,mismatch)) -> unequalLength<>mismatch | _ -> false
        | _ -> false
    let guard = graph.Nodes.TryFind c.Guard |> Option.bind (Operations.operation graph) |> Option.exists (fun (_,operation,operands,_) ->
        match operation,operands with NumericOperationKind.Less,[index;length] -> refTo c.Index index && length=c.LeftLength | _ -> false)
    calleeMatches graph c.Negated c.Callee && kind c.Site=Some(SemanticKind.Sequential [c.LeftBinding;c.RightBinding;c.Decision]) &&
    binding false ((=) c.Left) c.LeftBinding && binding false ((=) c.Right) c.RightBinding &&
    refTo c.LeftBinding c.LeftSource && refTo c.RightBinding c.RightSource &&
    kind c.LeftView=Some(SemanticKind.StringByteBorrow c.LeftSource) && kind c.RightView=Some(SemanticKind.StringByteBorrow c.RightSource) &&
    length c.LeftSource c.LeftLength && length c.RightSource c.RightLength &&
    op NumericOperationKind.Equal [c.LeftLength;c.RightLength] c.LengthTest &&
    binding true (integer 0L) c.Index && binding true (bool true) c.Equal && guard && refTo c.Index c.Current &&
    op NumericOperationKind.Equal [c.LeftRead;c.RightRead] c.ByteTest && advance && stop && branchValuesDistinct &&
    kind c.Body=Some(SemanticKind.IfThenElse(c.ByteTest,c.Advance,Some c.Stop)) &&
    kind c.Loop=Some(SemanticKind.WhileLoop(c.Guard,c.Body)) && refTo c.Equal c.Result && decision &&
    (c.Members |> List.forall (fun id -> graph.Nodes.TryFind id |> Option.exists owned))
