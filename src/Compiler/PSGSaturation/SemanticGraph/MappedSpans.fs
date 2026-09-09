/// Shared declaration facts for mapped-view guards and their bounded span proof.
module Clef.Compiler.PSGSaturation.SemanticGraph.MappedSpans

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution

/// Base alignment need not be the alignment of every scalar element. For
/// example, a 32-byte aligned u32 base only guarantees 4-byte element alignment.
let forLayout graph (layout: BorrowedViews.Layout) : Result<MappedSpanModel, string> =
    match cAbiOfGraph graph with
    | [(_, bits, _)] when bits = 32 || bits = 64 ->
        let bytes = layout.ElementBits / 8
        if bytes <= 0 || layout.ElementBits % 8 <> 0 || layout.Alignment <= 0 then
            Error "Mapped span requires byte-sized elements and positive declared alignment."
        else
            Ok { PointerBits = bits; MaximumExtent = (1I <<< (bits - 1)) - 1I
                 ElementBytes = bytes; BaseAlignment = layout.Alignment
                 ElementAlignment = int (System.Numerics.BigInteger.GreatestCommonDivisor(bigint bytes, bigint layout.Alignment)) }
    | _ -> Error "Mapped span requires one supported declared C pointer representation."

let ofMapping graph (mapping: MappedBindings.DeclaredMapping) =
    mapping.Parameters
    |> List.tryPick (fun (_, ty, id) -> if id = mapping.CallbackParameter then Some (applySubst ty) else None)
    |> function
        | Some (NativeType.TFun (view, _)) -> BorrowedViews.layout graph view |> Result.bind (forLayout graph)
        | _ -> Error "Mapped span requires its declared view callback."

/// Cite the actual schema and ABI declarations, alongside the mapping record.
let declarationSources graph (mapping: MappedBindings.DeclaredMapping) =
    graph.Nodes.Values |> Seq.choose (fun binding ->
        match binding.Kind, List.tryLast binding.Children with
        | SemanticKind.Binding _, Some body ->
            recordOf graph body |> Option.bind (fun (node, fields) ->
                match typeName node with
                | Some "CAbiDescriptor" -> Some node.Id
                | Some "ViewLayoutDescriptor" when field "Schema" fields |> Option.bind (stringOf graph) = Some mapping.Layout -> Some node.Id
                | _ -> None)
        | _ -> None) |> Seq.toList
