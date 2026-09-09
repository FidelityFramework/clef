namespace Clef.Compiler.Service.Tests

open Xunit

// CCS checking currently shares node/type counters across calls, including dimensional tests.
[<assembly: CollectionBehavior(DisableTestParallelization = true)>]
do ()

type ModuleScopeTests() =
    static member Cases =
        ModuleScopeCases.tests |> Seq.map (fun (name, _) -> [| box name |])

    [<Theory; MemberData(nameof ModuleScopeTests.Cases)>]
    [<Trait("Category", "Compiler.Service"); Trait("Subcategory", "ModuleScope")>]
    member _.``Module scope semantics``(name: string) =
        ModuleScopeCases.tests |> List.find (fun (testName, _) -> testName = name) |> snd |> fun test -> test ()
