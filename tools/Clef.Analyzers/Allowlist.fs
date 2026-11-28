// clef #165 Increment B - the checked-in ANALYZER-POLICY Option A allowlist.
//
// Governing authority:
//   https://forge.spkez.dev/FidelityFramework/clef/issues/165 (comments #11768, #12618, #12645)
//   https://forge.spkez.dev/FidelityFramework/clef/wiki/Compiler-Core-Boundary-and-Saturation-Recovery
//     sections 1, 2 (PP-2), 3.2, 3.3
//   Farscape ADL ad188177: ZONE-A-ANALYZER-BOUNDARY, ANALYZER-POLICY (Option A),
//                          AUDITED-CLOSURE, COLLOQUIUM-CONVERGENCE-AND-TRIAGE,
//                          PLAIN-ENGINEERING-TERMS
//
// Option A is default-refuse for both BCL and FSharp.Core: every BCL or
// FSharp.Core entity/member reached from Zone A is refused unless it is named
// in the narrow checked-in allowlist below (excluding explicitly banned members
// such as Operators.box/unbox/lock/isNull/typeof/failwith/exit and
// HashIdentity.Reference).  There is no blanket System.Array exemption and
// direct System.String members are refused.
module ClefAnalyzerAllowlist

open System

/// Zone A roots inside src/Compiler (recovery wiki section 1).
let zoneRoots = [ "NativeTypedTree/"; "PSGSaturation/"; "Baker/"; "Nanopass/" ]

/// Analyser fixtures are exercised without editing src/, so they are treated as
/// Zone A sources by path.
let fixtureMarker = "tools/Clef.Analyzers/tests/fixtures"

/// Primitive value carriers.  Referring to these types is admitted; calling a
/// member on them is not (see admittedMembers below).
let primitiveCarriers =
  Set.ofList [ "System.String"; "System.Char"; "System.Boolean"; "System.Byte"; "System.SByte"
               "System.Int16"; "System.Int32"; "System.Int64"; "System.UInt16"; "System.UInt32"
               "System.UInt64"; "System.Numerics.BigInteger"; "System.Decimal"; "System.Single"
               "System.Double" ]

/// The only BCL entities admitted by name.  System.StringComparison is the
/// primitive comparison carrier used by the ordered traversals; the array type
/// itself is admitted as a carrier, never as a member source.
let admittedEntities =
  Set.ofList [ "System.StringComparison"; "System.Array" ]

/// The only BCL members admitted in Zone A: the array length property.  Every
/// other BCL member is refused (ANALYZER-POLICY Option A, "no blanket
/// System.Array exemption").
let admittedMembers =
  Set.ofList [ ("System.Array", "get_Length"); ("System.Array", "Length") ]

/// Narrow checked-in allowlist of pure FSharp.Core modules, algebraic carriers,
/// and compile-time metadata attributes (ANALYZER-POLICY Option A, #12618).
/// Operators.Unchecked, FSharpRef, Control.*, Quotations.*, NativeInterop.*,
/// ReferenceEqualityAttribute, AllowNullLiteralAttribute, and VolatileFieldAttribute
/// are intentionally excluded (default-refuse).
let admittedFSharpCoreExact =
  Set.ofList [
    "Microsoft.FSharp.Core.Operators"
    "Microsoft.FSharp.Core.Operators.OperatorFunctions"
    "Microsoft.FSharp.Core.Operators.Checked"
    "Microsoft.FSharp.Core.ExtraTopLevelOperators"
    "Microsoft.FSharp.Core.LanguagePrimitives"
    "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions"
    "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicOperators"
    "Microsoft.FSharp.Core.LanguagePrimitives.ErrorStrings"
    "Microsoft.FSharp.Core.StringModule"
    "Microsoft.FSharp.Core.OptionModule"
    "Microsoft.FSharp.Core.ValueOptionModule"
    "Microsoft.FSharp.Core.ResultModule"
    "Microsoft.FSharp.Core.Unit"
    "Microsoft.FSharp.Core.FuncConvert"
    "Microsoft.FSharp.Core.OptimizedClosures"
    "Microsoft.FSharp.Core.PrintfModule"
    "Microsoft.FSharp.Core.Printf"
    "Microsoft.FSharp.Core.NumericLiterals"
    "Microsoft.FSharp.Core.NumericLiterals.NumericLiteralI"
    "Microsoft.FSharp.Core.NumericLiterals.NumericLiteralG"
    "Microsoft.FSharp.Core.CompilerServices.RuntimeHelpers"
    "Microsoft.FSharp.Core.CompilerServices.ListCollector"
    "Microsoft.FSharp.Core.CompilerServices.ArrayCollector"
    "Microsoft.FSharp.Core.CompilerServices.MeasureInverse"
    "Microsoft.FSharp.Core.CompilerServices.MeasureProduct"
    "Microsoft.FSharp.Core.CompilerServices.MeasureOne"
    "Microsoft.FSharp.Collections.ListModule"
    "Microsoft.FSharp.Collections.ArrayModule"
    "Microsoft.FSharp.Collections.Array2DModule"
    "Microsoft.FSharp.Collections.Array3DModule"
    "Microsoft.FSharp.Collections.Array4DModule"
    "Microsoft.FSharp.Collections.SeqModule"
    "Microsoft.FSharp.Collections.SetModule"
    "Microsoft.FSharp.Collections.MapModule"
    "Microsoft.FSharp.Collections.StringModule"
    "Microsoft.FSharp.Collections.ComparisonIdentity"
    "Microsoft.FSharp.Collections.HashIdentity"
    // Pure compile-time F# metadata attributes (excluding ReferenceEquality,
    // AllowNullLiteral, and VolatileField).
    "Microsoft.FSharp.Core.AutoOpenAttribute"
    "Microsoft.FSharp.Core.CompiledNameAttribute"
    "Microsoft.FSharp.Core.StructAttribute"
    "Microsoft.FSharp.Core.ClassAttribute"
    "Microsoft.FSharp.Core.InterfaceAttribute"
    "Microsoft.FSharp.Core.AbstractClassAttribute"
    "Microsoft.FSharp.Core.SealedAttribute"
    "Microsoft.FSharp.Core.RequireQualifiedAccessAttribute"
    "Microsoft.FSharp.Core.LiteralAttribute"
    "Microsoft.FSharp.Core.NoComparisonAttribute"
    "Microsoft.FSharp.Core.NoEqualityAttribute"
    "Microsoft.FSharp.Core.CustomComparisonAttribute"
    "Microsoft.FSharp.Core.CustomEqualityAttribute"
    "Microsoft.FSharp.Core.StructuralEqualityAttribute"
    "Microsoft.FSharp.Core.StructuralComparisonAttribute"
    "Microsoft.FSharp.Core.InlineIfLambdaAttribute"
    "Microsoft.FSharp.Core.CLIMutableAttribute"
    "Microsoft.FSharp.Core.DefaultValueAttribute"
    "Microsoft.FSharp.Core.CompilationRepresentationAttribute"
    "Microsoft.FSharp.Core.CompilationRepresentationFlags"
    "Microsoft.FSharp.Core.CompilationArgumentCountsAttribute"
    "Microsoft.FSharp.Core.CompilationMappingAttribute"
    "Microsoft.FSharp.Core.SourceConstructFlags"
    "Microsoft.FSharp.Core.EntryPointAttribute"
    "Microsoft.FSharp.Core.NoDynamicInvocationAttribute"
    "Microsoft.FSharp.Core.GeneralizableValueAttribute"
    "Microsoft.FSharp.Core.TailCallAttribute"
    "Microsoft.FSharp.Core.ExperimentalAttribute"
    "Microsoft.FSharp.Core.UnverifiableAttribute"
    "Microsoft.FSharp.Core.MeasureAttribute"
    "Microsoft.FSharp.Core.MeasureAnnotatedAbbreviationAttribute"
    "Microsoft.FSharp.Core.AutoSerializableAttribute"
    "Microsoft.FSharp.Core.ProjectionParameterAttribute"
    "Microsoft.FSharp.Core.ReflectedDefinitionAttribute"
    "Microsoft.FSharp.Core.StructLayoutAttribute"
  ]

/// Generic pure FSharp.Core algebraic types matched across all arities (`prefix` or `prefix``N`).
let admittedFSharpCoreGenericBases =
  [ "Microsoft.FSharp.Core.FSharpOption"
    "Microsoft.FSharp.Core.FSharpValueOption"
    "Microsoft.FSharp.Core.FSharpResult"
    "Microsoft.FSharp.Core.FSharpChoice"
    "Microsoft.FSharp.Core.FSharpFunc"
    "Microsoft.FSharp.Core.FSharpTypeFunc"
    "Microsoft.FSharp.Core.PrintfFormat"
    "Microsoft.FSharp.Core.StringFormat"
    "Microsoft.FSharp.Core.Format"
    "Microsoft.FSharp.Core.CompilerServices.ListCollector"
    "Microsoft.FSharp.Core.CompilerServices.ArrayCollector"
    "Microsoft.FSharp.Core.OptimizedClosures.FSharpFunc"
    "Microsoft.FSharp.Collections.FSharpList"
    "Microsoft.FSharp.Collections.FSharpSet"
    "Microsoft.FSharp.Collections.FSharpMap" ]

let isAdmittedFSharpCoreEntity (name: string) =
  admittedFSharpCoreExact.Contains name
  || admittedFSharpCoreGenericBases
     |> List.exists (fun prefix ->
          name = prefix || name.StartsWith(prefix + "`", StringComparison.Ordinal))

/// CLF001 single topological publication driver allowlist (recovery wiki
/// section 1 remedy 2 and section 2 PP-2).  Internal calls within a module's
/// own source file are admitted by canonical file comparison in Analyzer.fs;
/// cross-module re-invocations in consumers (including BoundaryEmission.fs and
/// WitnessEmission.fs) are detected and ratcheted.  Any new file added here
/// requires an explicit owner ruling.
let publicationDrivers =
  Set.ofList [ "NativeTypedTree/NativeService.fs" ]

let isBclAssembly (assembly: string) =
  assembly = "System"
  || assembly.StartsWith("System.", StringComparison.Ordinal)
  || assembly = "netstandard"
  || assembly = "mscorlib"
  || (assembly.StartsWith("Microsoft.", StringComparison.Ordinal)
      && not (assembly.StartsWith("Microsoft.FSharp.", StringComparison.Ordinal)))

let isFSharpCoreAssembly (assembly: string) = assembly = "FSharp.Core"
