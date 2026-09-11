/// Declaration predicates retain their source expression and dependencies.
/// This first fragment decides closed integer/Boolean relations. Calls,
/// mutable storage, conversions and runtime facts remain pending.
module Clef.Compiler.PSGSaturation.SemanticGraph.Predicates

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core

type Value = Integer of bigint | Boolean of bool

/// Follow immutable declaration references and record projections only. In
/// particular, a mutable binding's initializer is not its current value.
let resolve (graph: SemanticGraph) (dependencies: System.Collections.Generic.HashSet<NodeId>) id =
    let rec follow seen id =
        if Set.contains id seen then None else
        dependencies.Add id |> ignore
        let seen = Set.add id seen
        match SemanticGraph.tryGetNode id graph with
        | Some { Kind = SemanticKind.TypeAnnotation(inner, _) }
        | Some { Kind = SemanticKind.Quote(inner, _) } -> follow seen inner
        | Some { Kind = SemanticKind.VarRef(_, Some binding) } ->
            dependencies.Add binding |> ignore
            match SemanticGraph.tryGetNode binding graph with
            | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> follow (Set.add binding seen) value
            | _ -> None
        | Some { Kind = SemanticKind.FieldGet(subject, name) } ->
            match follow seen subject with
            // This fragment observes declaration records only. A record
            // reachable by runtime code may have mutable fields or aliases;
            // its initializer cannot establish their later contents.
            | Some { Kind = SemanticKind.RecordExpr(fields, _); IsReachable = false } ->
                fields |> List.tryFind (fst >> (=) name) |> Option.bind (snd >> follow seen)
            | _ -> None
        | value -> value
    follow Set.empty id

let valueOf graph id = resolve graph (System.Collections.Generic.HashSet<NodeId>()) id

let evaluate (graph: SemanticGraph) id =
    let dependencies = System.Collections.Generic.HashSet<NodeId>()
    let rec eval seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        let nested = eval seen
        match resolve graph dependencies id with
        | Some { Kind = SemanticKind.Literal(NativeLiteral.Int(v, _)) } -> Some(Integer(bigint v))
        | Some { Kind = SemanticKind.Literal(NativeLiteral.UInt(v, _)) } -> Some(Integer(bigint v))
        | Some { Kind = SemanticKind.Literal(NativeLiteral.Bool v) } -> Some(Boolean v)
        | Some { Kind = SemanticKind.IfThenElse(condition, yes, Some no) } ->
            match nested condition with
            | Some(Boolean true) -> nested yes
            | Some(Boolean false) -> nested no
            | _ -> None
        | Some ({ Kind = SemanticKind.Application(fn, args) } as application) ->
            match resolve graph dependencies fn with
            | Some { Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.Operators; Operation = op } } ->
                let sealedArithmetic =
                    List.contains op ["op_UnaryNegation"; "op_Addition"; "op_Subtraction"; "op_Multiply"; "op_Division"; "op_Modulus"] &&
                    (match Clef.Compiler.NativeTypedTree.NativeTypes.Types.tryGetNTUKind application.Type with
                     | Some(NTUKind.NTUint(NTUWidth.Fixed _)) | Some(NTUKind.NTUuint(NTUWidth.Fixed _)) -> true
                     | _ -> false)
                // Fixed-width wrapping/saturation is a different relation.
                // Do not silently give it mathematical-integer semantics.
                match op, (if sealedArithmetic then [] else List.map nested args) with
                | "op_UnaryNegation", [Some(Integer a)] -> Some(Integer(-a))
                | "not", [Some(Boolean a)] -> Some(Boolean(not a))
                | "op_Addition", [Some(Integer a); Some(Integer b)] -> Some(Integer(a + b))
                | "op_Subtraction", [Some(Integer a); Some(Integer b)] -> Some(Integer(a - b))
                | "op_Multiply", [Some(Integer a); Some(Integer b)] -> Some(Integer(a * b))
                | "op_Division", [Some(Integer a); Some(Integer b)] when b <> 0I -> Some(Integer(a / b))
                | "op_Modulus", [Some(Integer a); Some(Integer b)] when b <> 0I -> Some(Integer(a % b))
                | "op_LessThan", [Some(Integer a); Some(Integer b)] -> Some(Boolean(a < b))
                | "op_LessThanOrEqual", [Some(Integer a); Some(Integer b)] -> Some(Boolean(a <= b))
                | "op_GreaterThan", [Some(Integer a); Some(Integer b)] -> Some(Boolean(a > b))
                | "op_GreaterThanOrEqual", [Some(Integer a); Some(Integer b)] -> Some(Boolean(a >= b))
                | "op_Equality", [Some(Integer a); Some(Integer b)] -> Some(Boolean(a = b))
                | "op_Equality", [Some(Boolean a); Some(Boolean b)] -> Some(Boolean(a = b))
                | "op_Inequality", [Some(Integer a); Some(Integer b)] -> Some(Boolean(a <> b))
                | "op_Inequality", [Some(Boolean a); Some(Boolean b)] -> Some(Boolean(a <> b))
                | "op_BooleanAnd", [Some(Boolean a); Some(Boolean b)] -> Some(Boolean(a && b))
                | "op_BooleanOr", [Some(Boolean a); Some(Boolean b)] -> Some(Boolean(a || b))
                | _ -> None
            | _ -> None
        | _ -> None
    eval Set.empty id, dependencies |> Seq.sort |> Seq.toList

let integerOf graph id =
    match fst (evaluate graph id) with Some(Integer n) -> Some n | _ -> None

let condition graph name declaration expression source : PredicateEvidence =
    let value, dependencies = evaluate graph expression
    let status, message =
        match value with
        | Some(Boolean true) -> Established, "closed Clef relation established"
        | Some(Boolean false) -> Contradicted, "closed Clef relation contradicted"
        | _ -> Pending, "requires information outside the supported immutable integer/Boolean fragment"
    { Name = name; Declaration = declaration; Expression = expression
      Dependencies = dependencies; Status = status; Message = message; Source = source }
