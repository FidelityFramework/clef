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
module CallableIngress = Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress

/// Canonical identity stops at a formal: each invocation carries its own extent.
/// Origin enumeration follows the existing complete callable-flow relation.
let stringOrigin (graph: SemanticGraph) (flow: CallableOrigins.Resolution) source =
    let formalInputs = CallableIngress.closedFormalInputs graph flow (CallableIngress.analyzeWith graph flow)
    let rec canonical seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.VarRef(_, Some binding) } -> canonical seen binding
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> canonical seen value
        | Some { Kind = SemanticKind.TypeAnnotation(value, _) } -> canonical seen value
        | Some { Kind = SemanticKind.Literal(NativeLiteral.String _) }
        | Some { Kind = SemanticKind.PatternBinding _ } -> Some(id, seen)
        | _ -> None
    let rec origins seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.Literal(NativeLiteral.String text) } ->
            Some(Map.ofList [id, bigint (System.Text.Encoding.UTF8.GetByteCount text)], Set.singleton id)
        | Some { Kind = SemanticKind.VarRef(_, Some binding) } -> origins seen binding |> Option.map (fun (values, participants) -> values, Set.add id participants)
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] }
        | Some { Kind = SemanticKind.TypeAnnotation(value, _) } -> origins seen value |> Option.map (fun (values, participants) -> values, Set.add id participants)
        | Some { Kind = SemanticKind.PatternBinding _ } ->
            match formalInputs id with
            | Some ingress ->
                ingress.Inputs |> List.fold (fun state (call, actual) ->
                    match state, flow.Calls.TryFind call, origins seen actual with
                    | Some(values, participants), Some resolved, Some(more, dependencies) when resolved.Complete && not resolved.Unknown ->
                        let joint = resolved.Targets |> List.collect (fun target -> target.Lambda :: target.Body :: target.Arguments @ (target.Parameters |> List.map (fun (_, _, formal) -> formal))) |> Set.ofList
                        Some(Map.fold (fun acc key value -> Map.add key value acc) values more,
                             Set.unionMany [participants; dependencies; joint; ingress.Participants; Set.ofList [id; call; actual]])
                    | _ -> None) (Some(Map.empty, Set.singleton id))
            | _ -> None
        | _ -> None
    match canonical Set.empty source, origins Set.empty source with
    | Some(identity, path), Some(values, participants) -> Some(identity, values, Set.union path participants)
    | _ -> None

let private owned (node: SemanticNode) = node.Metadata.TryFind "Baker.StringComparisonOwned" = Some(MetadataValue.Bool true)

let private zeroEvidence graph left right =
    let flow = CallableOrigins.resolve graph
    [left;right] |> List.choose (fun source ->
        stringOrigin graph flow source |> Option.bind (fun (_,origins,participants) ->
            if not origins.IsEmpty && origins.Values |> Seq.forall ((=) 0I) then Some participants else None))
    |> function [] -> None | facts -> Some(Set.unionMany facts)

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

let materialize (graph: SemanticGraph) (source: SemanticNode, kind, callee, left, right) =
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
    let empty = zeroEvidence graph left right
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

let private calleeMatches graph negated callee =
    match BoundaryDeclarations.target graph callee with
    | Some({ Kind=SemanticKind.Intrinsic { Module=IntrinsicModule.Operators; Operation=operation } },_) ->
        operation=(if negated then "op_Inequality" else "op_Equality")
    | _ -> false

let validLengthStructure (graph: SemanticGraph) (c: LengthConstruction) =
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
    length c.LeftSource c.LeftLength && length c.RightSource c.RightLength && test && decision &&
    zeroEvidence graph c.Left c.Right=Some(Set.ofList c.Evidence)

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
