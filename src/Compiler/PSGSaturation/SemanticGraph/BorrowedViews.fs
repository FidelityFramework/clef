/// Schema-bound views of foreign storage. A view has no public constructor and
/// no address operation; a declared mapping scope supplies the bounded value.
module Clef.Compiler.PSGSaturation.SemanticGraph.BorrowedViews

open System.Runtime.CompilerServices
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution

type Layout = {
    Schema: string
    ElementBits: int
    Range: ValueRange
    Alignment: int
    Access: string
}

let isView ty = Types.tryGetNTUKind (applySubst ty) = Some NTUKind.NTUborrowedview

let private schemasUncached (graph: SemanticGraph) =
    graph.Nodes.Values
    |> Seq.choose (fun binding ->
        match binding.Kind, List.tryLast binding.Children with
        | SemanticKind.Binding _, Some body ->
            match recordOf graph body with
            | Some (node, fields) when typeName node = Some "ViewLayoutDescriptor" ->
                let stringField name = field name fields |> Option.bind (stringOf graph)
                match stringField "Schema", stringField "Element", field "Alignment" fields |> Option.bind (int64Of graph), stringField "Access" with
                | Some schema, Some repr, Some alignment, Some access ->
                    let scalar =
                        match repr with
                        | BAREWire.Hardware.Repr.U8 -> Some (8, ValueRange.unsignedOf 8) | BAREWire.Hardware.Repr.I8 -> Some (8, ValueRange.twosComplement 8)
                        | BAREWire.Hardware.Repr.U16 -> Some (16, ValueRange.unsignedOf 16) | BAREWire.Hardware.Repr.I16 -> Some (16, ValueRange.twosComplement 16)
                        | BAREWire.Hardware.Repr.U32 -> Some (32, ValueRange.unsignedOf 32) | BAREWire.Hardware.Repr.I32 -> Some (32, ValueRange.twosComplement 32)
                        | BAREWire.Hardware.Repr.U64 -> Some (64, ValueRange.unsignedOf 64) | BAREWire.Hardware.Repr.I64 -> Some (64, ValueRange.twosComplement 64)
                        | _ -> None
                    let permission =
                        match access with
                        | BAREWire.Hardware.AccessKind.ReadOnly -> Some "ReadOnly"
                        | BAREWire.Hardware.AccessKind.WriteOnly -> Some "WriteOnly"
                        | BAREWire.Hardware.AccessKind.ReadWrite -> Some "ReadWrite"
                        | _ -> None
                    let value =
                        match scalar, permission with
                        | Some (bits, range), Some permission when alignment > 0L && alignment <= int64 System.Int32.MaxValue
                                                  && (alignment &&& (alignment - 1L)) = 0L
                                                  ->
                            Ok { Schema = schema; ElementBits = bits; Range = range; Alignment = int alignment; Access = permission }
                        | _ -> Error (sprintf "View schema '%s' requires a supported integer element, power-of-two alignment and declared access." schema)
                    Some (schema, value)
                | Some schema, _, _, _ -> Some (schema, Error (sprintf "View schema '%s' has a malformed ViewLayoutDescriptor." schema))
                | _ -> None
            | _ -> None
        | _ -> None)
    |> Seq.groupBy fst
    |> Seq.map (fun (name, rows) ->
        let values = rows |> Seq.map snd |> Seq.distinct |> Seq.toList
        name, (match values with [one] -> one | _ -> Error (sprintf "View schema '%s' has conflicting layout declarations." name)))
    |> Map.ofSeq

let private cache = ConditionalWeakTable<SemanticGraph, Map<string, Result<Layout, string>>>()
let private schemas graph = cache.GetValue(graph, fun graph -> schemasUncached graph)

let layout (graph: SemanticGraph) (ty: NativeType) : Result<Layout, string> =
    match applySubst ty with
    | NativeType.TApp (tc, [schema]) when tc.NTUKind = Some NTUKind.NTUborrowedview ->
        match applySubst schema with
        | NativeType.TApp (schemaType, []) ->
            match Map.tryFind schemaType.Name (schemas graph) with
            | Some found -> found
            | None ->
                let matches = schemas graph |> Map.toList |> List.filter (fun (name, _) ->
                    name.Split('.') |> Array.last = (schemaType.Name.Split('.') |> Array.last))
                match matches with
                | [(_, found)] -> found
                | [] -> Error (sprintf "BorrowedView schema '%s' has no ViewLayoutDescriptor." schemaType.Name)
                | _ -> Error (sprintf "BorrowedView schema '%s' is ambiguous; qualify its declaration." schemaType.Name)
        | _ -> Error "BorrowedView requires a concrete nominal schema at native realization."
    | _ -> Error "Expected a BorrowedView type."

let operation (graph: SemanticGraph) (nodeId: NodeId) =
    match SemanticGraph.tryGetNode nodeId graph with
    | Some { Kind = SemanticKind.Application (fn, view :: arguments) } ->
        match valueOf graph fn, SemanticGraph.tryGetNode view graph with
        | Some { Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.BorrowedView; Operation = op } }, Some source ->
            Some (op, view, arguments, layout graph source.Type)
        | _ -> None
    | _ -> None

/// The physical load is a declared boundary. Set checks the original value
/// before narrowing; it intentionally has no pre-call truncation meet.
let numericBoundary (graph: SemanticGraph) nodeId : DeclaredParameter option =
    match operation graph nodeId with
    | Some ("get", _, _, Ok view) ->
        Some { Node = nodeId; Name = "BorrowedView.get"; Bits = view.ElementBits; Range = view.Range }
    | Some (("length" | "stride") as name, _, _, Ok view) ->
        graph.Platform |> Option.bind (fun context -> PlatformContext.tryWidth context "Pointer" |> Result.toOption)
        |> Option.map (fun pointerBits ->
            // Mapping realization admits only spans representable by the
            // signed pointer-sized extent model. Stride additionally carries
            // its producers' actual native out-parameter declaration.
            let extentRange = ValueRange.Bounded (0I, (1I <<< (pointerBits - 1)) - 1I)
            let producers =
                if name <> "stride" then [] else
                (MappedBindings.read graph).Mappings
                |> List.filter (fun mapping -> mapping.Layout = view.Schema)
                |> List.choose (fun mapping ->
                    match mapping.RowStride with
                    | MappedBindings.Output parameter ->
                        mapping.AcquireParameters |> List.tryFind (fun (name, _, _) -> name = parameter)
                        |> Option.bind (fun (_, _, id) -> mapping.Acquire.References |> List.tryFind (fun (p, _) -> p = id) |> Option.map snd)
                    | _ -> None)
            let bits, range =
                match producers with
                | [] -> pointerBits, extentRange
                | declarations ->
                    let maxBits = declarations |> List.map (fun d -> d.Bits) |> List.max
                    let declared = declarations |> List.map (fun d -> d.Range) |> List.reduce ValueRange.join
                    min pointerBits maxBits, ValueRange.meet extentRange declared
            { Node = nodeId; Name = "BorrowedView." + name; Bits = bits; Range = range })
    | _ -> None
