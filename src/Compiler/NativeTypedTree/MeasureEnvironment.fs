/// The measure environment: the declared measures, each abbreviation's expansion computed once, and
/// the failure value every measure diagnostic is made from.
///
/// Design of record: docs/fidelity/phg/Dimensional_Step1_2_Design.md (a.3), (a.4), (f) CCS8042 to
/// CCS8050; docs/fidelity/phg/Dimensional_Steps_1_2_Sequence.md CS-2.
///
/// A sibling of DimensionAlgebra.fs rather than an addition to it: the algebra is the group and its
/// unifier, this file is the declaration table. Like the algebra it is compiled before NativeTypes.fs
/// and knows no type DU and no syntax. The translation of an abbreviation's right-hand side needs the
/// type table (a name found as a type is CCS8045), so the translator lives in Expressions/Types.fs
/// and reaches registration as a parameter; registration decides the order, the cycle and the
/// parameter refusal, and the translator decides what a body denotes.
///
/// Wiring is not in this changeset (sequence CS-2): nothing registers into this environment yet.
/// The `[<Measure>] type` declaration arm in NativeService.fs still falls through to a class
/// definition, and `TypeEnv.Measures` stays empty; CS-4 redirects the declaration arm here.
module Clef.Compiler.NativeTypedTree.MeasureEnvironment

open Clef.Compiler.Text
open Clef.Compiler.NativeTypedTree.DimensionAlgebra

//-------------------------------------------------------------------------
// The failure value
//-------------------------------------------------------------------------

/// Why a measure declaration or a measure expression is refused. A value, never a default: each
/// case carries what its message names and the range the diagnostic is reported at. The CCS code
/// and the design (f) message are projected from it in one place, `describeMeasureFailure` in
/// Expressions/Types.fs beside `DiagnosticCodes`, so no code string is spelled here.
[<RequireQualifiedAccess>]
type MeasureFailure =
    /// CCS8042. `name` (as written) is neither a declared measure nor a type.
    | NotInScope of name: string * range: range
    /// CCS8043. Resolving the abbreviation `name` reaches `name` again; `chain` runs from `name`
    /// back to `name`, in the order the bodies were followed.
    | Cyclic of name: string * chain: string list * range: range
    /// CCS8044. A measure variable in a literal's annotation, `1.0<'u>`. Minted by the literal
    /// resolver when it reads the annotation (CS-4); no producer in this changeset.
    | VariableInLiteral of name: string * range: range
    /// CCS8045. `arg` (as written) is a type where a measure is required, or a measure where a
    /// type is required.
    | SortMismatch of arg: string * range: range
    /// CCS8046. A measure was applied to `ty`, which carries no dimension.
    | NoDimension of ty: string * range: range
    /// CCS8048. The rational exponent `r` (as written).
    | RationalExponent of r: string * range: range
    /// CCS8048 family. The integer exponent `n`, written or reached by a power of a power, is
    /// beyond the bound the translator keeps so the algebra's `int` arithmetic cannot overflow
    /// (`Expressions/Types.fs`, `measureExponentBound`).
    | ExponentOutOfRange of n: string * range: range
    /// CCS8049. The measure definition `name` declares type or measure parameters, or its body
    /// mentions a measure variable it does not declare.
    | Parameterised of name: string * range: range
    /// CCS8050. `tycon` takes one measure argument; `given` were written.
    | ArityMismatch of tycon: string * given: int * range: range

//-------------------------------------------------------------------------
// Definitions
//-------------------------------------------------------------------------

/// A declared measure (design a.3): a primitive generator, `[<Measure>] type m`, or an abbreviation,
/// `[<Measure>] type N = kg m / s^2`, whose right-hand side was translated once, at declaration,
/// through the environment as it then stood. An abbreviation never appears in a `Dimension`; a
/// reference to it denotes its stored expansion.
type MeasureDef =
    | Primitive of BaseMeasure
    | Abbreviation of BaseMeasure * expansion: Dimension

module MeasureDef =

    /// The declaration identity.
    let measure (def: MeasureDef) : BaseMeasure =
        match def with
        | Primitive b
        | Abbreviation(b, _) -> b

    /// The dimension a reference to the definition denotes.
    let dimension (def: MeasureDef) : Dimension =
        match def with
        | Primitive b -> Dimension.ofBase b
        | Abbreviation(_, expansion) -> expansion

/// One `[<Measure>] type` declaration as registration receives it. `Body` is `None` for a primitive
/// and the right-hand side for an abbreviation; the right-hand side's type is the registrant's own
/// (a syntax node in the checker), which is why this module reads nothing of it. `Parameters` are
/// the declared type or measure parameter names; any is refused, CCS8049.
type MeasureDecl<'body> =
    { Measure: BaseMeasure
      Parameters: string list
      Body: 'body option
      Range: range }

//-------------------------------------------------------------------------
// The environment
//-------------------------------------------------------------------------

/// The declared measures, keyed by declaration identity. `Declared` is the same set in order of
/// declaration, most recent first: a written name resolves to the most recent declaration it
/// matches, as a later declaration shadows an earlier one of the same name.
type MeasureEnv =
    { Defs: Map<BaseMeasure, MeasureDef>
      Declared: BaseMeasure list }

module MeasureEnv =

    /// No measures declared.
    let empty : MeasureEnv = { Defs = Map.empty; Declared = [] }

    /// Whether a written path denotes the declaration `b`: the last segment is its name and the
    /// qualifying prefix, if any, is a suffix of its declaring module path (`Physics.m` names the
    /// `m` declared in `...Physics`; `m` names any `m` in scope).
    let private denotes (path: string list) (b: BaseMeasure) : bool =
        match List.rev path with
        | [] -> false
        | name :: revQualifier ->
            let qualifier = List.rev revQualifier
            name = b.Name
            && qualifier.Length <= b.Module.Length
            && qualifier = List.skip (b.Module.Length - qualifier.Length) b.Module

    /// The definition a written path denotes, if any.
    let tryFind (path: string list) (env: MeasureEnv) : MeasureDef option =
        env.Declared
        |> List.tryFind (denotes path)
        |> Option.bind (fun b -> Map.tryFind b env.Defs)

    /// The environment with one more definition, shadowing any earlier one of the same identity.
    let private add (def: MeasureDef) (env: MeasureEnv) : MeasureEnv =
        let b = MeasureDef.measure def
        { Defs = Map.add b def env.Defs
          Declared = b :: List.filter (fun d -> d <> b) env.Declared }

    /// Register a declaration group (design a.3, (h) 3): a single declaration, or the members of
    /// one `type ... and ...` group, which may refer to each other in any order.
    ///
    /// The group is ordered before anything is translated. `references` lists the bare names a
    /// body mentions (the registrant's syntax-aware listing; this module reads no syntax), and a
    /// member is placed after every member it references. That order is what makes "translated
    /// once, through the environment as it stands" true and safe: when a body is read, every
    /// sibling it names is already registered, so a sibling that redeclares a name visible in the
    /// outer environment shadows it before any body can bind to the outer one. A reference that
    /// leads back to a member still being ordered is the cycle, CCS8043, with the chain of names
    /// that closed it, reported at the declaration the cycle returns to. A declaration with
    /// parameters is refused before its body is read, CCS8049; so is a body whose expansion is not
    /// ground, because a measure variable there is a parameter the declaration does not declare.
    ///
    /// The result is the grown environment or the first failure; nothing is registered on failure
    /// (per-declaration reporting is the declaration arm's concern, sequence CS-4).
    let registerGroup
        (references: 'body -> string list)
        (translate: MeasureEnv -> 'body -> Result<Dimension, MeasureFailure>)
        (decls: MeasureDecl<'body> list)
        (env: MeasureEnv)
        : Result<MeasureEnv, MeasureFailure> =

        let member' (name: string) : MeasureDecl<'body> option =
            decls |> List.tryFind (fun d -> d.Measure.Name = name)

        let placed (ordered: MeasureDecl<'body> list) (decl: MeasureDecl<'body>) : bool =
            ordered |> List.exists (fun d -> d.Measure = decl.Measure)

        /// Depth-first placement: a member follows the group members its body references.
        /// `visiting` is the chain of members whose placement is in progress, innermost first.
        let rec place (visiting: string list) (ordered: MeasureDecl<'body> list) (decl: MeasureDecl<'body>) : Result<MeasureDecl<'body> list, MeasureFailure> =
            if placed ordered decl then
                Ok ordered
            else
                let name = decl.Measure.Name
                let visiting' = name :: visiting
                let dependencies =
                    match decl.Body with
                    | None -> []
                    | Some body -> references body |> List.distinct |> List.choose member'
                dependencies
                |> List.fold
                    (fun acc dependency ->
                        acc
                        |> Result.bind (fun ordered' ->
                            let target = dependency.Measure.Name
                            if List.contains target visiting' then
                                let chain = (List.rev visiting' |> List.skipWhile (fun n -> n <> target)) @ [ target ]
                                Error(MeasureFailure.Cyclic(target, chain, dependency.Range))
                            else
                                place visiting' ordered' dependency))
                    (Ok ordered)
                |> Result.map (fun ordered' -> ordered' @ [ decl ])

        /// One declaration, in an environment where every sibling it references is registered.
        let registerOne (env: MeasureEnv) (decl: MeasureDecl<'body>) : Result<MeasureEnv, MeasureFailure> =
            let name = decl.Measure.Name
            match decl.Parameters, decl.Body with
            | _ :: _, _ -> Error(MeasureFailure.Parameterised(name, decl.Range))
            | [], None -> Ok(add (Primitive decl.Measure) env)
            | [], Some body ->
                translate env body
                |> Result.bind (fun expansion ->
                    if Dimension.isGround expansion then
                        Ok(add (Abbreviation(decl.Measure, expansion)) env)
                    else
                        Error(MeasureFailure.Parameterised(name, decl.Range)))

        decls
        |> List.fold (fun acc decl -> acc |> Result.bind (fun ordered -> place [] ordered decl)) (Ok [])
        |> Result.bind (fun ordered ->
            ordered |> List.fold (fun acc decl -> acc |> Result.bind (fun env' -> registerOne env' decl)) (Ok env))
