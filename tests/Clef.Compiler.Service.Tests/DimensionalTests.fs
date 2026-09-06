namespace Clef.Compiler.Service.Tests

open Xunit

/// Clef measure algebra, inference, identity, and diagnostic regressions.
type DimensionalTests() =
    static member Cases =
        DimensionalCases.tests |> Seq.map (fun (name, _) -> [| box name |])

    [<Theory; MemberData(nameof DimensionalTests.Cases)>]
    [<Trait("Category", "Compiler.Service"); Trait("Subcategory", "Dimensions")>]
    member _.``Dimensional semantics``(name: string) =
        DimensionalCases.tests |> List.find (fun (testName, _) -> testName = name) |> snd |> fun test -> test ()
