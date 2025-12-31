// Copyright (c) SpeakEZ Technologies. Licensed under the Apache License, Version 2.0.
// Native type system for FNCS - no BCL, no IL imports, no obj.

namespace FSharp.Native.Compiler.Checking

open System.Collections.Generic

/// Module path for symbol resolution
[<Struct>]
type ModulePath = 
    { Namespace: string list
      Module: string }
    
    static member Root = { Namespace = []; Module = "" }
    
    member this.FullName = 
        match this.Namespace with
        | [] -> this.Module
        | ns -> String.concat "." ns + "." + this.Module

/// Type layout - determines memory representation
[<RequireQualifiedAccess>]
type TypeLayout =
    /// Stack-allocated, known size and alignment
    | Inline of size: int * align: int
    /// Arena-allocated (heap)
    | Reference of arena: ArenaAffinity
    /// Platform-specific (e.g., native pointers)
    | Opaque

/// Arena affinity for memory management
and [<RequireQualifiedAccess>] ArenaAffinity =
    /// Default: current actor's arena
    | CurrentActor
    /// Named arena
    | Explicit of name: string
    /// Stack allocation (no arena)
    | Stack

/// Type constructor reference (not IL-based)
type TypeConRef = 
    { Name: string
      Module: ModulePath
      Arity: int
      Layout: TypeLayout }

/// Type parameter state for Union-Find
[<RequireQualifiedAccess>]
type TypeParamState =
    | Unbound
    | Bound of NativeType

/// Type parameter with constraints and Union-Find parent pointer
and TypeParam = 
    { Id: int
      Name: string
      mutable Constraints: Constraint list
      /// Union-Find parent pointer for efficient substitution
      mutable Parent: TypeParamState }
    
    /// Create a fresh unbound type parameter
    static member Fresh(id: int, name: string) =
        { Id = id; Name = name; Constraints = []; Parent = TypeParamState.Unbound }

/// The native type representation
and [<RequireQualifiedAccess>] NativeType =
    /// Universally quantified type: forall 'a 'b. T
    | TForall of TypeParam list * NativeType
    /// Type application: List<int>, option<string>
    | TApp of TypeConRef * NativeType list
    /// Tuple type: int * string * bool
    | TTuple of NativeType list * isStruct: bool
    /// Function type: 'a -> 'b
    | TFun of domain: NativeType * range: NativeType
    /// Type variable (for inference)
    | TVar of TypeParam
    /// Unit of measure
    | TMeasure of Measure
    /// Anonymous record: {| Name: string; Age: int |}
    | TAnon of AnonRecordType
    /// Byref type: byref<'T>, inref<'T>, outref<'T>
    | TByref of NativeType * ByrefKind

/// Byref kinds
and [<RequireQualifiedAccess>] ByrefKind =
    | In      // inref<'T> - read-only reference
    | Out     // outref<'T> - write-only reference
    | InOut   // byref<'T> - read-write reference

/// Measure type for units of measure
and [<Struct>] Measure =
    { BaseMeasures: Map<string, int> }  // e.g., m^2/s = {m: 2, s: -1}
    
    static member Dimensionless = { BaseMeasures = Map.empty }
    
    member this.IsDimensionless = this.BaseMeasures.IsEmpty

/// Anonymous record type
and AnonRecordType =
    { Fields: (string * NativeType) list
      IsStruct: bool }

/// Constraints generated during type checking
and [<RequireQualifiedAccess>] Constraint =
    /// Type equality: t1 = t2
    | Equals of NativeType * NativeType * range: Range
    /// SRTP member constraint: ^T has member M with signature S
    | HasMember of ty: NativeType * memberName: string * signature: NativeType * range: Range
    /// Measure constraint
    | HasMeasure of NativeType * Measure * range: Range
    /// Subtype constraint (minimal, for class inheritance)
    | Subtype of sub: NativeType * super: NativeType * range: Range
    /// Layout compatibility constraint
    | LayoutCompatible of NativeType * TypeLayout * range: Range

/// Source range (line, column, file)
and [<Struct>] Range =
    { StartLine: int
      StartColumn: int
      EndLine: int
      EndColumn: int
      FileName: string }
    
    static member Zero = { StartLine = 0; StartColumn = 0; EndLine = 0; EndColumn = 0; FileName = "" }

/// Memory region for UMX-style phantom types
[<RequireQualifiedAccess>]
type MemoryRegion =
    | Sram
    | Flash
    | Peripheral
    | Dma
    | Arena of name: string

/// Access kind for pointers
[<RequireQualifiedAccess>]
type AccessKind =
    | ReadOnly
    | WriteOnly
    | ReadWrite

/// Native pointer type with region and access annotations
type NativePtr =
    { PointeeType: NativeType
      Region: MemoryRegion
      Access: AccessKind }

/// Node identifier for semantic graph
[<Struct>]
type NodeId = 
    | NodeId of int
    
    member this.Value = let (NodeId v) = this in v

/// Literal values
[<RequireQualifiedAccess>]
type LiteralValue =
    | Unit
    | Bool of bool
    | Int8 of int8
    | UInt8 of uint8
    | Int16 of int16
    | UInt16 of uint16
    | Int32 of int32
    | UInt32 of uint32
    | Int64 of int64
    | UInt64 of uint64
    | Float32 of float32
    | Float64 of float
    | Char of char
    | String of string  // UTF-8 encoded
    | Null  // Only for interop, should error in native code

/// Module for NodeId operations
module NodeId =
    let mutable private counter = 0
    
    let fresh () =
        let id = System.Threading.Interlocked.Increment(&counter)
        NodeId id
    
    let reset () =
        counter <- 0

/// Module for TypeParam operations
module TypeParam =
    let mutable private counter = 0
    
    let fresh (name: string) =
        let id = System.Threading.Interlocked.Increment(&counter)
        TypeParam.Fresh(id, name)
    
    let freshAnon () =
        let id = System.Threading.Interlocked.Increment(&counter)
        TypeParam.Fresh(id, sprintf "'T%d" id)
    
    let reset () =
        counter <- 0
