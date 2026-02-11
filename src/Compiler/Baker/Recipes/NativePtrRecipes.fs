// Copyright (c) 2025-2026 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// Baker NativePtr Recipes - Transformation of NativePtr to MemRef intrinsics.
///
/// ARCHITECTURAL PRINCIPLE: F# Semantics → MLIR Semantics at Baker Boundary
///
/// This module implements the CRITICAL transformation that eliminates NativePtr
/// from MiddleEnd. NativePtr is an F# abstraction; MemRef is MLIR semantics.
///
/// TRANSFORMATION RULES:
/// - NativePtr.stackalloc<'T> count → MemRef.alloca count : memref<?x'T>
/// - NativePtr.read ptr → MemRef.load ptr 0n : 'T (scalar load at index 0)
/// - NativePtr.write ptr value → MemRef.store value ptr 0n (scalar store at index 0)
/// - NativePtr.add ptr offset → Flattened: downstream write/read uses offset directly
/// - NativePtr.copy dest src count → MemRef.copy dest src count
///
/// POST-TRANSFORMATION STATE:
/// - PSG contains ONLY MemRef Application nodes (no NativePtr)
/// - All offsets are nativeint (maps to MLIR index type)
/// - Alex witnesses MemRef operations as pure memref MLIR (no casts, no LLVM cruft)
///
/// See: /home/hhh/.claude/plans/zippy-kindling-nova.md
/// See: Serena memory "architecture_principles"
module FSharp.Native.Compiler.Baker.Recipes.NativePtrRecipes

open FSharp.Native.Compiler.NativeTypedTree.NativeTypes
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Types
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Core
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Elaboration
open FSharp.Native.Compiler.Baker.Recipes.Decomposition

//-------------------------------------------------------------------------
// Node Construction Helpers
//-------------------------------------------------------------------------

/// Create a MemRef intrinsic node
let private mkMemRefIntrinsic (operation: string) (ty: NativeType) (range: SourceRange) (ctx: Context) : SemanticNode =
    let intrinsicInfo = {
        Module = IntrinsicModule.MemRef
        Operation = operation
        Category = IntrinsicCategory.Memory
        FullName = "MemRef." + operation
    }
    { Id = NodeId.fresh()
      Kind = SemanticKind.Intrinsic intrinsicInfo
      Range = range
      Type = ty
      SRTPResolution = None
      ArenaAffinity = ArenaAffinity.CurrentActor
      LayoutHint = None
      Children = []
      Parent = None
      Metadata = Map.empty
      IsReachable = true
      EmissionStrategy = EmissionStrategy.Inline }
    |> markBaker operation ctx.ExpansionId

/// Create an Application node with MemRef intrinsic
let private mkMemRefApplication
    (operation: string)
    (funcTy: NativeType)
    (resultTy: NativeType)
    (args: NodeId list)
    (range: SourceRange)
    (ctx: Context)
    : SemanticNode list * NodeId =

    let funcNode = mkMemRefIntrinsic operation funcTy range ctx
    let appNode =
        { Id = NodeId.fresh()
          Kind = SemanticKind.Application (funcNode.Id, args)
          Range = range
          Type = resultTy
          SRTPResolution = None
          ArenaAffinity = ArenaAffinity.CurrentActor
          LayoutHint = None
          Children = funcNode.Id :: args
          Parent = None
          Metadata = Map.empty
          IsReachable = true
          EmissionStrategy = EmissionStrategy.Inline }
        |> markBaker operation ctx.ExpansionId

    ([funcNode; appNode], appNode.Id)

/// Create a literal nativeint node (for zero index in scalar load/store)
let private mkNativeIntLiteral (value: int64) (range: SourceRange) (ctx: Context) : SemanticNode =
    { Id = NodeId.fresh()
      Kind = SemanticKind.Literal (NativeLiteral.Int (value, NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Pointer)))
      Range = range
      Type = Types.nintType
      SRTPResolution = None
      ArenaAffinity = ArenaAffinity.CurrentActor
      LayoutHint = None
      Children = []
      Parent = None
      Metadata = Map.empty
      IsReachable = true
      EmissionStrategy = EmissionStrategy.Inline }
    |> markBaker "ScalarIndex" ctx.ExpansionId

//-------------------------------------------------------------------------
// Transformation Functions
//-------------------------------------------------------------------------

/// Transform NativePtr.stackalloc<'T> count → MemRef.alloca count
let private transformStackAlloc
    (countArg: NodeId)
    (elemType: NativeType)
    (range: SourceRange)
    (ctx: Context)
    : SemanticNode list * NodeId =

    // Type: nativeint -> memref<?x'T>
    let funcTy = NativeType.TFun(Types.nintType, NativeType.TNativePtr elemType)
    let resultTy = NativeType.TNativePtr elemType

    mkMemRefApplication "alloca" funcTy resultTy [countArg] range ctx

/// Transform NativePtr.read ptr → MemRef.load ptr 0n (scalar load)
let private transformRead
    (ptrArg: NodeId)
    (elemType: NativeType)
    (range: SourceRange)
    (ctx: Context)
    : SemanticNode list * NodeId =

    // Create literal 0n for index
    let zeroNode = mkNativeIntLiteral 0L range ctx

    // Type: memref<?x'T> -> nativeint -> 'T
    let funcTy = NativeType.TFun(NativeType.TNativePtr elemType, NativeType.TFun(Types.nintType, elemType))
    let resultTy = elemType

    let nodes, resultId = mkMemRefApplication "load" funcTy resultTy [ptrArg; zeroNode.Id] range ctx
    (zeroNode :: nodes), resultId

/// Transform NativePtr.write ptr value → MemRef.store value ptr 0n (scalar store)
let private transformWrite
    (ptrArg: NodeId)
    (valueArg: NodeId)
    (elemType: NativeType)
    (range: SourceRange)
    (ctx: Context)
    : SemanticNode list * NodeId =

    // Create literal 0n for index
    let zeroNode = mkNativeIntLiteral 0L range ctx

    // Type: 'T -> memref<?x'T> -> nativeint -> unit
    let funcTy = NativeType.TFun(elemType, NativeType.TFun(NativeType.TNativePtr elemType, NativeType.TFun(Types.nintType, Types.unitType)))
    let resultTy = Types.unitType

    let nodes, resultId = mkMemRefApplication "store" funcTy resultTy [valueArg; ptrArg; zeroNode.Id] range ctx
    (zeroNode :: nodes), resultId

/// Transform NativePtr.add base offset → FLATTENED (returns base, offset used downstream)
///
/// CRITICAL: NativePtr.add is NOT a real operation in memref semantics.
/// It's F#'s way of expressing "I want to index this pointer".
/// In MLIR memref, there is no "pointer + offset" operation - indexing happens
/// at load/store sites.
///
/// HOWEVER, we can't just "delete" this node, because downstream write/read
/// expects to consume it. So we transform it to a MemRef.add that Alex will
/// recognize as a special indexing marker.
///
/// Alex will witness MemRef.add by extracting the offset argument and using it
/// in subsequent MemRef.store/load operations.
let private transformAdd
    (baseArg: NodeId)
    (offsetArg: NodeId)
    (elemType: NativeType)
    (range: SourceRange)
    (ctx: Context)
    : SemanticNode list * NodeId =

    // For now, we create a MemRef.add node that carries both base and offset.
    // Alex will extract the offset when witnessing downstream store/load.
    // This is a MARKER operation, not a real MLIR operation.

    // Type: memref<?x'T> -> nativeint -> memref<?x'T>
    let funcTy = NativeType.TFun(NativeType.TNativePtr elemType, NativeType.TFun(Types.nintType, NativeType.TNativePtr elemType))
    let resultTy = NativeType.TNativePtr elemType

    mkMemRefApplication "add" funcTy resultTy [baseArg; offsetArg] range ctx

/// Transform NativePtr.copy dest src count → MemRef.copy dest src count
let private transformCopy
    (destArg: NodeId)
    (srcArg: NodeId)
    (countArg: NodeId)
    (elemType: NativeType)
    (range: SourceRange)
    (ctx: Context)
    : SemanticNode list * NodeId =

    // Type: memref<?x'T> -> memref<?x'T> -> nativeint -> unit
    let funcTy = NativeType.TFun(NativeType.TNativePtr elemType,
                    NativeType.TFun(NativeType.TNativePtr elemType,
                        NativeType.TFun(Types.nintType, Types.unitType)))
    let resultTy = Types.unitType

    mkMemRefApplication "copy" funcTy resultTy [destArg; srcArg; countArg] range ctx

//-------------------------------------------------------------------------
// PUBLIC API: tryTransform
//-------------------------------------------------------------------------

/// Try to transform a NativePtr operation to MemRef operation.
/// Returns Some (Result) if transformation succeeds, None if operation is not recognized.
let tryTransform
    (operation: string)
    (args: NodeId list)
    (returnType: NativeType)
    (range: SourceRange)
    (ctx: Context)
    (graph: SemanticGraph)
    : Result option =

    match operation, args with
    | "stackalloc", [countArg] ->
        // Extract element type from return type (nativeptr<'T>)
        let elemType =
            match returnType with
            | NativeType.TNativePtr ty -> ty
            | _ -> failwith "NativePtr.stackalloc: expected nativeptr<'T> return type"

        let nodes, resultId = transformStackAlloc countArg elemType range ctx
        Some (mkResultNoShadow nodes resultId [])

    | "read", [ptrArg] ->
        // Element type is the return type ('T)
        let elemType = returnType
        let nodes, resultId = transformRead ptrArg elemType range ctx
        Some (mkResultNoShadow nodes resultId [])

    | "write", [ptrArg; valueArg] ->
        // Extract element type from pointer type
        let ptrNode = SemanticGraph.tryGetNode ptrArg graph
        let elemType =
            match ptrNode with
            | Some node ->
                match node.Type with
                | NativeType.TNativePtr ty -> ty
                | _ -> failwith "NativePtr.write: expected nativeptr<'T> for first argument"
            | None -> failwith "NativePtr.write: could not resolve pointer argument"

        let nodes, resultId = transformWrite ptrArg valueArg elemType range ctx
        Some (mkResultNoShadow nodes resultId [])

    | "add", [baseArg; offsetArg] ->
        // Extract element type from return type (nativeptr<'T>)
        let elemType =
            match returnType with
            | NativeType.TNativePtr ty -> ty
            | _ -> failwith "NativePtr.add: expected nativeptr<'T> return type"

        let nodes, resultId = transformAdd baseArg offsetArg elemType range ctx
        Some (mkResultNoShadow nodes resultId [])

    | "copy", [destArg; srcArg; countArg] ->
        // Extract element type from dest pointer type
        let destNode = SemanticGraph.tryGetNode destArg graph
        let elemType =
            match destNode with
            | Some node ->
                match node.Type with
                | NativeType.TNativePtr ty -> ty
                | _ -> failwith "NativePtr.copy: expected nativeptr<'T> for dest argument"
            | None -> failwith "NativePtr.copy: could not resolve dest argument"

        let nodes, resultId = transformCopy destArg srcArg countArg elemType range ctx
        Some (mkResultNoShadow nodes resultId [])

    // Operations we don't transform (may need to add more later)
    | "get", _
    | "set", _
    | "toNativeInt", _
    | "ofNativeInt", _
    | "toVoidPtr", _
    | "ofVoidPtr", _
    | "fill", _ ->
        None  // Not yet implemented - fail loudly if encountered

    | _, _ ->
        None  // Unknown operation
