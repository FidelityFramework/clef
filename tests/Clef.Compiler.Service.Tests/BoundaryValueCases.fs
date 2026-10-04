namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

module private BoundaryValuesFixture =
    let check source =
        match parseAndCheck ("module BoundaryValues\n" + source) "boundary-values.clef" with
        | Success result | CheckFailure result -> result
        | ParseFailure errors -> failwithf "Boundary value source did not parse: %A" errors
    let nativeGraph pointerBits =
        let source = """module BoundaryValues
type Listener = { Entry: FnPtr<bool -> bool> }
let callback (enabled: bool) : bool = enabled
[<EntryPoint>]
let main _ =
    let listener = { Entry = FnPtr.ofFunction callback }
    if FnPtr.invoke listener.Entry true then 0 else 1
"""
        SourcePlatformFixture.check pointerBits "boundary-values.clef" source

    let publish graph =
        match Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph with
        | Result.Ok revision -> revision
        | Result.Error failures -> failwithf "Native component publication refused: %A" failures

    let nativeContract (graph: SemanticGraph) =
        graph.Codata.Value.CallableContracts.Values
        |> Seq.filter (fun contract -> contract.Kind = CallableKind.NativeEntry)
        |> Assert.Single

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "BoundaryValues")>]
type BoundaryValueCases() =
    [<Theory>]
    [<InlineData("[<EntryPoint>]\nlet main _ = let mutable value = true in let address = &&value in 0")>]
    [<InlineData("let raw (value: bool) = &&value\n[<EntryPoint>]\nlet main _ = 0")>]
    [<InlineData("let raw (value: bool byref) = &&value\n[<EntryPoint>]\nlet main _ = 0")>]
    member _.``A source raw address is rejected even when its result is unused`` source =
        let result = BoundaryValuesFixture.check source
        Assert.Contains(result.Diagnostics, fun diagnostic ->
            diagnostic.Code = "CCS8401" && diagnostic.Severity = NativeDiagnosticSeverity.Error && diagnostic.Message.Contains("Raw addresses"))
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8401" && Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error)
        Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
            match node.Type with NativeType.TNativePtr _ -> true | _ -> false)

    [<Theory>]
    [<InlineData("Sys.stackArgv")>]
    [<InlineData("Arena.fromPointer")>]
    [<InlineData("Arena.alloc")>]
    [<InlineData("Arena.allocAligned")>]
    member _.``Internal address ingredients are unavailable through source lookup`` name =
        let result = BoundaryValuesFixture.check ($"let unavailable () = {name}\n[<EntryPoint>]\nlet main _ = 0\n")
        Assert.Contains(result.Diagnostics, fun diagnostic ->
            diagnostic.Code = "CCS8401" && Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error)
        Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
            match node.Kind with
            | SemanticKind.Intrinsic info -> info.FullName = name
            | _ -> false)

    [<Theory>]
    [<InlineData("let handle: CHandle<unit> = NativeDefault.zeroed ()", "if handle = handle then 0 else 1")>]
    [<InlineData("let zero = NativeDefault.zeroed\nlet handle: CHandle<unit> = zero ()", "if handle = handle then 0 else 1")>]
    [<InlineData("let forge () : CHandle<unit> = NativeDefault.zeroed ()", "let handle = forge () in if handle = handle then 0 else 1")>]
    [<InlineData("let construct factory : CHandle<unit> = factory ()", "let handle = construct NativeDefault.zeroed in if handle = handle then 0 else 1")>]
    [<InlineData("type Holder<'T> = Entry of 'T\nlet construct holder : CHandle<unit> = match holder with Entry factory -> factory ()", "let handle = construct (Entry NativeDefault.zeroed) in if handle = handle then 0 else 1")>]
    [<InlineData("let construct candidate : option<CHandle<unit>> = match candidate with Some factory -> Some (factory ()) | None -> None", "match construct (Some NativeDefault.zeroed) with Some handle -> (if handle = handle then 0 else 1) | None -> 0")>]
    [<InlineData("let construct candidate : voption<CHandle<unit>> = match candidate with ValueSome factory -> ValueSome (factory ()) | ValueNone -> ValueNone", "match construct (ValueSome NativeDefault.zeroed) with ValueSome handle -> (if handle = handle then 0 else 1) | ValueNone -> 0")>]
    [<InlineData("let construct candidate : Result<CHandle<unit>, bool> = match candidate with Ok factory -> Ok (factory ()) | Error flag -> Error flag", "match construct (Ok NativeDefault.zeroed) with Ok handle -> (if handle = handle then 0 else 1) | Error flag -> if flag then 1 else 0")>]
    [<InlineData("type Holder<'T> = { Value: 'T }\nlet holder: Holder<CHandle<unit>> = NativeDefault.zeroed ()", "if holder.Value = holder.Value then 0 else 1")>]
    [<InlineData("type Inner = { Value: CHandle<unit> }\ntype Outer = { Nested: Inner }\nlet holder: Outer = NativeDefault.zeroed ()", "if holder.Nested.Value = holder.Nested.Value then 0 else 1")>]
    [<InlineData("let pair: CHandle<unit> * bool = NativeDefault.zeroed ()", "let handle, _ = pair in if handle = handle then 0 else 1")>]
    [<InlineData("type Wrapped = Wrapped of CHandle<unit>\nlet wrapped: Wrapped = NativeDefault.zeroed ()", "match wrapped with Wrapped handle -> if handle = handle then 0 else 1")>]
    [<InlineData("let wrapped: Result<CHandle<unit>, bool> = NativeDefault.zeroed ()", "match wrapped with Ok handle -> (if handle = handle then 0 else 1) | Error flag -> if flag then 1 else 0")>]
    [<InlineData("type Holder<'T> = { Value: 'T }\nlet holder: Holder<unit -> CHandle<unit>> = NativeDefault.zeroed ()", "let handle = holder.Value () in if handle = handle then 0 else 1")>]
    [<InlineData("type option = Wrapped of CHandle<unit>\nlet wrapped: option = NativeDefault.zeroed ()", "match wrapped with Wrapped handle -> if handle = handle then 0 else 1")>]
    [<InlineData("type voption = Wrapped of CHandle<unit>\nlet wrapped: voption = NativeDefault.zeroed ()", "match wrapped with Wrapped handle -> if handle = handle then 0 else 1")>]
    [<InlineData("let handle: CHandle<unit> = NativeDefault.zeroed ()", "let closure () = handle in let captured = closure () in if captured = captured then 0 else 1")>]
    [<InlineData("let pointer: FnPtr<unit -> unit> = NativeDefault.zeroed ()", "FnPtr.invoke pointer (); 0")>]
    [<InlineData("type Listener = { Entry: FnPtr<unit -> unit> }\nlet listener: Listener = NativeDefault.zeroed ()", "FnPtr.invoke listener.Entry (); 0")>]
    member _.``Zero initialization cannot forge a demanded non-null boundary value``(declarations: string, body: string) =
        let result = BoundaryValuesFixture.check (declarations + "\n[<EntryPoint>]\nlet main _ = " + body + "\n")
        Assert.Contains(result.Diagnostics, fun diagnostic ->
            diagnostic.Code = "CCS8010" && diagnostic.Severity = NativeDiagnosticSeverity.Error &&
            Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error && diagnostic.Message.Contains("NativeDefault.zeroed"))

    [<Theory>]
    [<InlineData("int")>]
    [<InlineData("CHandle<unit>")>]
    [<InlineData("option<CHandle<unit>>")>]
    [<InlineData("FnPtr<unit -> unit>")>]
    [<InlineData("int * int")>]
    member _.``FnPtr rejects a concrete payload without a function signature`` payload =
        let result = BoundaryValuesFixture.check ($"let invalid (pointer: FnPtr<{payload}>) = pointer\n[<EntryPoint>]\nlet main _ = 0\n")
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8096" && diagnostic.Message.Contains("requires a function signature"))
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8096" && Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error)

    [<Theory>]
    [<InlineData("type Alias<'T> = FnPtr<'T>\nlet invalid (pointer: Alias<int>) = pointer")>]
    [<InlineData("type Holder<'T> = { Entry: FnPtr<'T> }\nlet invalid (pointer: Holder<int>) = pointer")>]
    [<InlineData("type Holder<'T> = Entry of FnPtr<'T>\nlet invalid (pointer: Holder<int>) = pointer")>]
    member _.``Concrete instantiation cannot hide a non-function native signature`` source =
        let result = BoundaryValuesFixture.check (source + "\n[<EntryPoint>]\nlet main _ = 0\n")
        Assert.Contains(result.Diagnostics, fun diagnostic ->
            diagnostic.Code = "CCS8096" && Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error)

    [<Fact>]
    member _.``Absence and ordinary scalar records remain explicitly constructible``() =
        let result = BoundaryValuesFixture.check """
type Flags = { Enabled: bool }
let flags: Flags = NativeDefault.zeroed ()
let absent: option<CHandle<unit>> = None
[<EntryPoint>]
let main _ =
    match absent with
    | None -> if flags.Enabled then 1 else 0
    | Some handle -> if handle = handle then 1 else 0
"""
        DimensionalCases.noErrors result

    [<Theory>]
    [<InlineData(32)>]
    [<InlineData(64)>]
    member _.``Native entry records use the declared platform pointer width`` pointerBits =
        let graph = BoundaryValuesFixture.nativeGraph pointerBits
        let layout = graph.Layouts.Value.Values |> Seq.choose (function
            | SettledLayout.Record([field], Some bytes, Some alignment) when field.Name = "Entry" -> Some(field, bytes, alignment)
            | _ -> None) |> Assert.Single
        let field, bytes, alignment = layout
        // FFI §3.6.1 items 1/2: "A single-entry family needs no code storage"
        // and each inhabited slot retains its receiving contract and lifetime.
        // Closure Representation §2.4 keeps native entries distinct and
        // explicitly without an ordinary closure environment.
        Assert.Equal(0, bytes)
        Assert.Equal(1, alignment)
        Assert.Equal(Some 0, field.Size)
        Assert.Equal(SettledSlot.InlineBytes(0, 1), field.Slot)
        let contract = BoundaryValuesFixture.nativeContract graph
        let convention =
            match contract.Convention with
            | CallableConvention.CompilerOwnedPortable convention -> convention
            | other -> failwithf "Expected compiler-owned portable convention: %A" other
        Assert.True(contract.EnvironmentBytes.IsNone)
        Assert.Empty contract.OmittedParameters
        Assert.Equal(Clef.Compiler.Baker.Ingredients.Boundaries.platformPremise graph.Platform, Some convention.Target)
        let lifetime = convention.CodeLifetime
        let expectedLifetime = [lifetime.Module; lifetime.Binding; lifetime.Implementation]
        let carriers = graph.Codata.Value.CallableCarriers.Values |> Seq.filter (fun carrier -> carrier.Kind = CallableKind.NativeEntry)
        Assert.NotEmpty carriers
        for carrier in carriers do
            Assert.Equal(Ok contract.Identity, carrier.Contract)
            Assert.True(carrier.Environment.IsNone)
            Assert.True(carrier.EnvironmentValue.IsNone)
            Assert.Equal<NodeId list>(expectedLifetime, carrier.Lifetime |> List.sortBy _.Ordinal |> List.map _.Node)
            Assert.All(carrier.Lifetime, fun participant ->
                Assert.Equal(ParticipantRole.CallableLifetime, participant.Role)
                Assert.Equal(contract.Identity, participant.Group))
        let revision = BoundaryValuesFixture.publish graph
        Assert.Empty(Fidelity.PSG.Integrity.callableAggregates revision)
        Assert.NotEmpty revision.Emission.Callable.AggregateDependencies
        // Standalone boundary carrier layout remains a separate assertion.
        Assert.Equal(TypeLayout.PlatformWord, layoutOf (NativeType.TApp(Types.fnPtrTyCon, [NativeType.TFun(Types.boolType, Types.boolType)])))

    [<Fact>]
    member _.``A native component without code residence is refused by its owning recipe`` () =
        let graph = BoundaryValuesFixture.nativeGraph 64
        let facts = graph.Codata.Value
        let carriers = facts.CallableCarriers |> Map.map (fun _ carrier ->
            if carrier.Kind = CallableKind.NativeEntry then { carrier with Lifetime = [] } else carrier)
        let settled =
            Clef.Compiler.Baker.Recipes.CallableAggregateRecipes.settle
                (Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolveCallableBranches graph)
                { Carriers = carriers; Contracts = facts.CallableContracts
                  Flows = facts.CallableFlows; Joins = facts.CallableJoins
                  PreviousSlots = facts.CallableAggregateSlots } graph
        Assert.Contains(settled.Residuals, fun failure -> failure.Code = "CCS8101")
        Assert.Empty settled.Values

    [<Fact>]
    member _.``A nonempty forged native lifetime cannot authorize an aggregate component`` () =
        let graph = BoundaryValuesFixture.nativeGraph 64
        let facts = graph.Codata.Value
        let unrelated = graph.Nodes.Values |> Seq.find (fun node ->
            match node.Kind with SemanticKind.TypeDef _ -> true | _ -> false)
        let carriers = facts.CallableCarriers |> Map.map (fun _ carrier ->
            if carrier.Kind <> CallableKind.NativeEntry then carrier else
            Assert.NotEmpty carrier.Lifetime
            let lifetime = carrier.Lifetime |> List.map (fun participant -> { participant with Node = unrelated.Id })
            { carrier with Lifetime = lifetime })
        let settled =
            Clef.Compiler.Baker.Recipes.CallableAggregateRecipes.settle
                (Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolveCallableBranches graph)
                { Carriers = carriers; Contracts = facts.CallableContracts
                  Flows = facts.CallableFlows; Joins = facts.CallableJoins
                  PreviousSlots = facts.CallableAggregateSlots } graph
        Assert.Contains(settled.Residuals, fun failure -> failure.Code = "CCS8101")
        Assert.Empty settled.Values
        let codata = { facts with CallableCarriers = carriers }
        let forged = { graph with Codata = lazy codata }
        Assert.True(Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare forged |> Result.isError)
        Assert.True(Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish forged |> Result.isError)

    [<Fact>]
    member _.``An extern-tagged binding cannot acquire compiler-owned code residence`` () =
        let graph = BoundaryValuesFixture.nativeGraph 64
        let contract = BoundaryValuesFixture.nativeContract graph
        let lifetime =
            match contract.Convention with
            | CallableConvention.CompilerOwnedPortable convention -> convention.CodeLifetime
            | other -> failwithf "Expected compiler-owned convention: %A" other
        let binding = graph.Nodes[lifetime.Binding]
        let externBinding =
            { binding with Metadata = binding.Metadata.Add("FidelityExtern.Library", MetadataValue.String "foreign-library") }
        let changed = { graph with Nodes = graph.Nodes.Add(binding.Id, externBinding) }
        Assert.True(Clef.Compiler.Baker.Ingredients.CompilerOwnedEntries.tryImplementation graph lifetime.Implementation |> Option.isSome)
        Assert.True(Clef.Compiler.Baker.Ingredients.CompilerOwnedEntries.tryImplementation changed lifetime.Implementation |> Option.isNone)
        Assert.True(Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish changed |> Result.isError)

    [<Theory>]
    [<InlineData(true)>]
    [<InlineData(false)>]
    member _.``Same identity native residence corruption withdraws the earlier account`` changeParent =
        let graph = BoundaryValuesFixture.nativeGraph 64
        let before = BoundaryValuesFixture.publish graph
        let contract = BoundaryValuesFixture.nativeContract graph
        let lifetime =
            match contract.Convention with
            | CallableConvention.CompilerOwnedPortable convention -> convention.CodeLifetime
            | other -> failwithf "Expected compiler-owned convention: %A" other
        let changed =
            if changeParent then
                let binding = graph.Nodes[lifetime.Binding]
                { graph with Nodes = graph.Nodes.Add(binding.Id, { binding with Parent = None }) }
            else
                let moduleNode = graph.Nodes[lifetime.Module]
                let kind =
                    match moduleNode.Kind with
                    | SemanticKind.ModuleDef(name, members) -> SemanticKind.ModuleDef(name, members |> List.filter ((<>) lifetime.Binding))
                    | other -> failwithf "Expected program module: %A" other
                { graph with Nodes = graph.Nodes.Add(moduleNode.Id, { moduleNode with Kind = kind }) }
        Assert.NotEmpty before.Emission.Callable.AggregateDependencies
        let sites = graph.Codata.Value.CallableAggregateDependencies.Keys |> Seq.toList
        Assert.NotEmpty sites
        for site in sites do
            Assert.True(Clef.Compiler.Baker.Ingredients.CallableAggregateAccounts.current changed site |> Result.isError)
        Assert.True(Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare changed |> Result.isError)
        Assert.True(Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish changed |> Result.isError)
