// SPDX-License-Identifier: MIT
module Clef.Compiler.Baker.Recipes.DeadBodyRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Operations = Clef.Compiler.Baker.Ingredients.NumericOperations

type private Constant = Integer of bigint | Boolean of bool

// Read current source result constants, retaining their evaluation in the rewrite.
// Neither a cached range nor an ordinary mutable initializer proves a later value.
let rec private constant (graph: SemanticGraph) initial seen id =
    if Set.contains id seen then None else
    let seen = Set.add id seen
    let read = constant graph initial seen
    match graph.Nodes.TryFind id with
    | Some { Kind = SemanticKind.Literal(NativeLiteral.Int(value,_)) } -> Some(Integer(bigint value))
    | Some { Kind = SemanticKind.Literal(NativeLiteral.Bool value) } -> Some(Boolean value)
    | Some { Kind = SemanticKind.TypeAnnotation(value,_) } -> read value
    | Some { Kind = SemanticKind.Sequential values; Children = children } when values=children ->
        List.tryLast values |> Option.bind read
    | Some { Kind = SemanticKind.VarRef(_,Some binding) } -> read binding
    | Some { Kind = SemanticKind.Binding(_,false,_,_); Children = [value] } -> read value
    | Some { Kind = SemanticKind.Binding(_,true,_,_); Children = [value] } when initial=Some id -> read value
    | Some node ->
        match Operations.operation graph node with
        | Some(_,NumericOperationKind.LogicalNot,[value],_) ->
            match read value with Some(Boolean value) -> Some(Boolean(not value)) | _ -> None
        | Some(_,kind,[left;right],_) ->
            match read left,read right with
            | Some(Integer left),Some(Integer right) ->
                match kind with
                | NumericOperationKind.Less -> Some(Boolean(left<right))
                | NumericOperationKind.LessOrEqual -> Some(Boolean(left<=right))
                | NumericOperationKind.Greater -> Some(Boolean(left>right))
                | NumericOperationKind.GreaterOrEqual -> Some(Boolean(left>=right))
                | NumericOperationKind.Equal -> Some(Boolean(left=right))
                | NumericOperationKind.NotEqual -> Some(Boolean(left<>right))
                | _ -> None
            | _ -> None
        | _ -> None
    | None -> None

// checkFor owns this ordered frontier: initialize the counter, evaluate the
// immutable bound, then test. The counter cannot be observed outside this loop;
// effects in either bound still execute, once and in their original order.
let private initialCounter (graph: SemanticGraph) (node: SemanticNode) guard =
    let rec descendants seen id =
        if Set.contains id seen then seen else
        graph.Nodes[id].Children |> List.fold descendants (Set.add id seen)
    let privateCounter counter =
        let owned = descendants Set.empty node.Id
        graph.Nodes.Values |> Seq.forall (fun source ->
            if owned.Contains source.Id then true else
            match source.Kind with
            | SemanticKind.VarRef(_,Some binding) | SemanticKind.CellAddress binding -> binding<>counter
            | SemanticKind.Lambda(_,_,captures,_,_) -> captures |> List.forall (fun capture -> capture.SourceNodeId<>Some counter)
            | _ -> true)
    match node.Parent |> Option.bind graph.Nodes.TryFind with
    | Some { Kind = SemanticKind.Sequential [counter;finish;loop]; Children = children }
        when loop=node.Id && children=[counter;finish;loop] ->
        match graph.Nodes.TryFind counter,graph.Nodes.TryFind finish,Operations.operation graph graph.Nodes[guard] with
        | Some { Kind = SemanticKind.Binding(_,true,_,_); Children = [_] },
          Some { Kind = SemanticKind.Binding(_,false,_,_); Children = [_] },
          Some(_,(NumericOperationKind.LessOrEqual | NumericOperationKind.GreaterOrEqual),[left;right],_) ->
            match graph.Nodes[left].Kind,graph.Nodes[right].Kind,constant graph None Set.empty finish with
            | SemanticKind.VarRef(_,Some actual),SemanticKind.VarRef(_,Some bound),Some(Integer _)
                when actual=counter && bound=finish && privateCounter counter -> Some counter
            | _ -> None
        | _ -> None
    | _ -> None

let replacement (graph: SemanticGraph) (node: SemanticNode) =
    let truth initial guard = constant graph initial Set.empty guard
    match node.Kind with
    | SemanticKind.IfThenElse(guard,yes,no) when node.Children=guard::yes::Option.toList no ->
        match truth None guard with
        | Some(Boolean true) -> Some(guard,Some yes)
        | Some(Boolean false) -> Some(guard,no)
        | _ -> None
    | SemanticKind.WhileLoop(guard,body) when node.Children=[guard;body] ->
        match truth (initialCounter graph node guard) guard with
        | Some(Boolean false) -> Some(guard,None)
        | _ -> None
    | _ -> None

let materialize (node: SemanticNode) (guard,selected) =
    let unitValue =
        {node with Id=NodeId.fresh(); Kind=SemanticKind.Literal NativeLiteral.Unit
                   Type=Types.unitType; Children=[]; Parent=Some node.Id; Metadata=Map.empty; ValueRange=None}
    let result = selected |> Option.defaultValue unitValue.Id
    let root =
        {node with Kind=SemanticKind.Sequential [guard;result]; Children=[guard;result]; ValueRange=None
                   Metadata=node.Metadata.Add(ElaborationMetadata.Kind,MetadataValue.String "Baker")
                                         .Add(ElaborationMetadata.For,MetadataValue.String "Source.dead-body")}
    root :: (if selected.IsNone then [unitValue] else [])
