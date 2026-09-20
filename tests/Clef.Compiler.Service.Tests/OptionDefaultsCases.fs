namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.DimensionAlgebra
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

module private OptionDefaults =
    let option payload = NativeType.TApp(Types.optionTyCon, [payload])
    let prelude = "module Dimensions\n[<Measure>] type m\n[<Measure>] type s\n"

    let check source =
        let result =
            match parseAndCheck (prelude + source) "dimensions.clef" with
            | Success result -> result
            | CheckFailure result -> failwithf "Expected successful checking: %A" result.Diagnostics
            | ParseFailure errors -> failwithf "Parse failed: %A" errors
        DimensionalCases.noErrors result
        Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
            match node.Kind with SemanticKind.Error _ -> true | _ -> false)
        Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.Intrinsic info -> info.Module = IntrinsicModule.Option && info.Operation = "defaultValue"
            | _ -> false)
        for node in result.Graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable) do
            for child in node.Children do
                Assert.True(result.Graph.Nodes.ContainsKey child, $"Dangling child {child} of {node.Id}")
        result

    /// Mark the exact expected diagnostic span with «...». Keep the rejected
    /// expression reachable: a diagnostic on a dead declaration is deliberately
    /// demoted and does not demonstrate rejection at the public pipeline boundary.
    let reject code (markedBody: string) =
        let start = markedBody.IndexOf('«')
        let finish = markedBody.IndexOf('»')
        Assert.True(start >= 0 && finish > start, "Expected one marked diagnostic span")
        let before = markedBody.Substring(0, start)
        let span = markedBody.Substring(start + 1, finish - start - 1)
        let position (text: string) =
            let lines = text.Split('\n')
            { Line = lines.Length; Column = (Array.last lines).Length }
        let file = "option-defaults-negative.clef"
        let expected =
            { File = file
              Start = position (prelude + before)
              End = position (prelude + before + span) }
        let body = markedBody.Replace("«", "").Replace("»", "")
        let source = prelude + body + "\n[<EntryPoint>]\nlet main _ = ignore wrong; 0\n"
        match parseAndCheck source file with
        | CheckFailure result ->
            Assert.True(CheckResult.hasErrors result)
            let diagnostics = result.Diagnostics |> List.filter (fun diagnostic ->
                diagnostic.Code = code && Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error)
            let diagnostic = Assert.Single diagnostics
            Assert.Equal<SourceRange>(expected, diagnostic.Range)
        | Success result ->
            failwithf "Invalid Option.defaultValue reached successful checking: %A" result.Diagnostics
        | ParseFailure errors ->
            failwithf "Expected located %s from checking, not a parser failure: %A" code errors

    let binding name (result: CheckResult) =
        result.Graph.Nodes.Values |> Seq.find (fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.Binding (actual, _, _, _) -> actual = name || actual.EndsWith("." + name)
            | _ -> false)

    let value name result = result.Graph.Nodes[(binding name result).Children.Head]

    let assertCall name (result: CheckResult) id =
        match result.Graph.Nodes[id].Kind with
        | SemanticKind.Application (callee, _) ->
            match result.Graph.Nodes[callee].Kind with
            | SemanticKind.VarRef (actual, _) -> Assert.True(actual = name || actual.EndsWith("." + name), actual)
            | kind -> failwithf "Expected reference to %s, got %A" name kind
        | kind -> failwithf "Expected call to %s, got %A" name kind

    let assertSelection (result: CheckResult) fallback optionId choice =
        let graph = result.Graph
        match graph.Nodes[choice].Kind with
        | SemanticKind.IfThenElse (guard, present, Some absent) ->
            Assert.Equal(fallback, absent)
            match graph.Nodes[present].Kind with
            | SemanticKind.DUEliminate (input, 1, "Some", payloadType) ->
                Assert.Equal(optionId, input)
                DimensionalCases.same graph.Nodes[fallback].Type payloadType
                DimensionalCases.same payloadType graph.Nodes[choice].Type
            | kind -> failwithf "Some branch lost its guarded extraction: %A" kind
            match graph.Nodes[guard].Kind with
            | SemanticKind.Application (_, [tag; expected]) ->
                match graph.Nodes[tag].Kind with
                | SemanticKind.DUGetTag (input, _) -> Assert.Equal(optionId, input)
                | kind -> failwithf "Guard did not inspect the same option: %A" kind
                match graph.Nodes[expected].Kind with
                | SemanticKind.Literal (NativeLiteral.Int (1L, _)) -> ()
                | kind -> failwithf "Guard did not select Some: %A" kind
            | kind -> failwithf "Expected tag comparison, got %A" kind
        | kind -> failwithf "Expected Some/None selection, got %A" kind

/// These check source typing, Baker structure and existing application evidence.
/// Native execution covers effect counts separately; no Option-specific theorem
/// or complete closure proof discharge is asserted here.
[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "OptionDefaults")>]
type OptionDefaultsTests() =
    [<Fact>]
    member _.``Default values retain independent payload types and dimensions``() =
        let result = OptionDefaults.check """
let present = Option.defaultValue 1<m> (Some 12<m>)
let absent = Option.defaultValue 3<s> None
let enabled = Option.defaultValue false (Some true)
let explicit = Option.defaultValue<int<m/s>> 2<m/s> None
[<EntryPoint>]
let main _ = if present = 12<m> && absent = 3<s> && enabled && explicit = 2<m/s> then 0 else 1
"""
        for name, expected in ["present", DimensionalCases.measuredInt DimensionalCases.metre;
                               "absent", DimensionalCases.measuredInt DimensionalCases.second;
                               "enabled", Types.boolType] do
            DimensionalCases.same expected (DimensionalCases.bindingType name result)

    [<Theory>]
    [<InlineData("let wrong = «Option.defaultValue 1<m> (Some 2<s>)»")>]
    [<InlineData("let stored = Option.defaultValue 1<m>\nlet wrong = «stored (Some 2<s>)»")>]
    [<InlineData("let choose = Option.defaultValue<int<m>>\nlet wrong = «choose 1<m> (Some 2<s>)»")>]
    member _.``Default values reject incompatible dimensions before witnessing``(source: string) =
        OptionDefaults.reject "CCS8040" source

    [<Theory>]
    [<InlineData("let wrong = «Option.defaultValue 1<m^-1> (Some 2<s^-1>)»", "CCS8040")>]
    [<InlineData("let wrong = «Option.defaultValue (6<m> / 2<s>) (Some (6<s> / 2<m>))»", "CCS8040")>]
    [<InlineData("let wrong = «Option.defaultValue (None: int<m> option) (Some (Some 1<s>))»", "CCS8040")>]
    [<InlineData("let stored = Option.defaultValue (None: int<m> option)\nlet wrong = «stored (Some (Some 1<s>))»", "CCS8040")>]
    [<InlineData("let wrong = «Option.defaultValue (fun (x: int<m>) -> x) (Some (fun (x: int<s>) -> x))»", "CCS8040")>]
    [<InlineData("let wrong = «Option.defaultValue (fun (_: unit) -> 1<m>) (Some (fun (_: unit) -> 1<s>))»", "CCS8040")>]
    [<InlineData("let stored = Option.defaultValue (fun (x: int<m>) -> x)\nlet wrong = «stored None 1<s>»", "CCS8040")>]
    [<InlineData("let wrong = «Option.defaultValue (fun (x: int<m>) -> x) (Some (fun (x: int<m>) (_: unit) -> x))»", "CCS8003")>]
    [<InlineData("let wrong = «Option.defaultValue 1<m> None 2<m>»", "CCS8003")>]
    [<InlineData("let wrong = «Option.defaultValue<int<m>, int<s>>»", "CCS8004")>]
    [<InlineData("let wrong = «Option.defaultValue<int<m>> 1<s>» None", "CCS8040")>]
    [<InlineData("let wrong = «Option.defaultValue 1<m> (Some 2.0<m>)»", "CCS8003")>]
    [<InlineData("let wrong = «Option.defaultValue 1<m> 2<m>»", "CCS8003")>]
    member _.``Nested payload and callable boundaries reject mismatches with located errors``(source: string, code: string) =
        OptionDefaults.reject code source

    [<Theory>]
    [<InlineData("let wrong = Option.defaultValue<float<«m^(1/2)»>>", "CCS8048")>]
    [<InlineData("let wrong = Option.defaultValue<float<«m^(-1/2)»>>", "CCS8048")>]
    [<InlineData("let wrong = Option.defaultValue 1.0<«m^(1/2)»> None", "CCS8048")>]
    [<InlineData("let wrong = Option.defaultValue («Math.sqrt 2.0<m>») None", "CCS8041")>]
    member _.``Current integer measure admission refuses written or inferred fractional exponents``(source: string, code: string) =
        // Fractional measure exponents are an admission extension, distinct from
        // exact fractional numeric values and from the NFT Neg/Recip constructors.
        OptionDefaults.reject code source

    [<Fact>]
    member _.``Negative measures and fractional numeric values survive different producers``() =
        let result = OptionDefaults.check """
let inverse = Option.defaultValue 1<m^-1> (Some (2 / 1<m>))
let speed = Option.defaultValue (6<m> / 2<s>) (Some (12<m> / 4<s>))
let fractional = Option.defaultValue -0.25<m^-1> (Some (1.0 / 2.0<m>))
let root = Option.defaultValue (Math.sqrt 4.0<m^2>) (Some 2.0<m>)
[<EntryPoint>]
let main _ =
    if inverse = 2<m^-1> && speed = 3<m/s> && fractional > 0.0<m^-1> && root > 0.0<m> then 0 else 1
"""
        let inverseDimension = Dimension.inv DimensionalCases.metre
        let speedDimension = Dimension.mul DimensionalCases.metre (Dimension.inv DimensionalCases.second)
        for name, expected in ["inverse", DimensionalCases.measuredInt inverseDimension;
                               "speed", DimensionalCases.measuredInt speedDimension;
                               "fractional", DimensionalCases.measured inverseDimension;
                               "root", DimensionalCases.measured DimensionalCases.metre] do
            DimensionalCases.same expected (DimensionalCases.bindingType name result)
        let literal, value = result.Graph.Nodes.Values |> Seq.pick (fun node ->
            match node.Metadata.TryFind "Numeric.RealLiteral" with
            | Some (MetadataValue.RealLiteral ("-0.25", value)) -> Some (node, value)
            | _ -> None)
        Assert.Equal(-1I, value.Numerator)
        Assert.Equal(4I, value.Denominator)
        Assert.True(literal.ValueRange.IsNone)
        DimensionalCases.same (DimensionalCases.measured inverseDimension) literal.Type

    [<Fact>]
    member _.``A shadowing declaration's dimension contract remains authoritative on failure``() =
        OptionDefaults.reject "CCS8040" "module Option =\n    let defaultValue (x: int<s>) = x\nlet wrong = «Option.defaultValue 1<m>»"

    [<Theory>]
    [<InlineData("module Option =\n    let defaultValue (x: int<m>) = x + 1<m>\nlet value = Option.defaultValue 2<m>")>]
    [<InlineData("type Surface = { defaultValue: int<m> -> int<m> }\nlet Option = { defaultValue = fun x -> x + 1<m> }\nlet value = Option.defaultValue 2<m>")>]
    member _.``Declared members and function fields keep lexical precedence``(source: string) =
        let result = OptionDefaults.check source
        DimensionalCases.same (DimensionalCases.measuredInt DimensionalCases.metre)
            (DimensionalCases.bindingType "value" result)

    [<Theory>]
    [<InlineData("Some 4<m>")>]
    [<InlineData("None")>]
    member _.``Both branches retain eager inputs and the same guarded option identity``(optionBody: string) =
        let result = OptionDefaults.check $"""
let fallback () = 7<m>
let input () : int<m> option = {optionBody}
let observed = Option.defaultValue (fallback ()) (input ())
[<EntryPoint>]
let main _ = if observed > 0<m> then 0 else 1
"""
        match (OptionDefaults.value "observed" result).Kind with
        | SemanticKind.Sequential [fallback; input; choice] ->
            OptionDefaults.assertCall "fallback" result fallback
            OptionDefaults.assertCall "input" result input
            OptionDefaults.assertSelection result fallback input choice
            Assert.Equal(Some (MetadataValue.String "Option.defaultValue"),
                result.Graph.Nodes[choice].Metadata.TryFind ElaborationMetadata.For)
        | kind -> failwithf "Default selection lost eager argument order: %A" kind

    [<Fact>]
    member _.``Forward pipe evaluates its option before the fallback expression``() =
        let result = OptionDefaults.check """
let fallback () = 7<m>
let input () = Some 4<m>
let observed = input () |> Option.defaultValue (fallback ())
[<EntryPoint>]
let main _ = if observed > 0<m> then 0 else 1
"""
        match (OptionDefaults.value "observed" result).Kind with
        | SemanticKind.Sequential [input; call] ->
            OptionDefaults.assertCall "input" result input
            match result.Graph.Nodes[call].Kind with
            | SemanticKind.Sequential [fallback; reusedInput; choice] ->
                Assert.Equal(input, reusedInput)
                OptionDefaults.assertCall "fallback" result fallback
                OptionDefaults.assertSelection result fallback input choice
            | kind -> failwithf "Piped default did not retain eager selection: %A" kind
        | kind -> failwithf "Forward pipe lost its input prerequisite: %A" kind

    [<Fact>]
    member _.``Partial formation snapshots the supplied value into one residual parameter``() =
        let result = OptionDefaults.check """
let mutable fallback: int<m> = 3<m>
[<EntryPoint>]
let main _ =
    let stored = Option.defaultValue fallback
    fallback <- 9<m>
    if stored None = 3<m> then 0 else 1
"""
        let graph = result.Graph
        let payloadType = DimensionalCases.measuredInt DimensionalCases.metre
        DimensionalCases.same (NativeType.TFun(OptionDefaults.option payloadType, payloadType))
            (DimensionalCases.bindingType "stored" result)
        match (OptionDefaults.value "stored" result).Kind with
        | SemanticKind.Sequential [snapshot; closure] ->
            match graph.Nodes[snapshot].Kind with
            | SemanticKind.Binding (_, false, false, _) -> ()
            | kind -> failwithf "Partial did not snapshot its fallback: %A" kind
            Assert.NotEqual((OptionDefaults.binding "fallback" result).Id, snapshot)
            match graph.Nodes[closure].Kind with
            | SemanticKind.Lambda (parameters, body, captures, _, _) ->
                let _, domain, _ = Assert.Single parameters
                DimensionalCases.same (OptionDefaults.option payloadType) domain
                let capture = Assert.Single captures
                Assert.Equal(Some snapshot, capture.SourceNodeId)
                Assert.False capture.IsMutable
                DimensionalCases.same payloadType capture.Type
                match graph.Nodes[body].Kind with
                | SemanticKind.IfThenElse (_, _, Some fallbackReference) ->
                    match graph.Nodes[fallbackReference].Kind with
                    | SemanticKind.VarRef (_, Some source) -> Assert.Equal(snapshot, source)
                    | kind -> failwithf "Residual lost snapshot identity: %A" kind
                | kind -> failwithf "Residual is not an option selection: %A" kind
            | kind -> failwithf "Partial did not become a closure: %A" kind
        | kind -> failwithf "Partial did not evaluate its fallback at formation: %A" kind

    [<Fact>]
    member _.``An option-valued fallback is a partial argument not the eliminated option``() =
        let result = OptionDefaults.check """
let stored = Option.defaultValue (None: int<m> option)
let present = stored (Some (Some 4<m>))
let absent = stored None
[<EntryPoint>]
let main _ = if Option.isSome present && Option.isNone absent then 0 else 1
"""
        let payload = OptionDefaults.option (DimensionalCases.measuredInt DimensionalCases.metre)
        DimensionalCases.same (NativeType.TFun(OptionDefaults.option payload, payload))
            (DimensionalCases.bindingType "stored" result)
        DimensionalCases.same payload (DimensionalCases.bindingType "present" result)
        DimensionalCases.same payload (DimensionalCases.bindingType "absent" result)

    [<Fact>]
    member _.``Bare default aliases specialize across types and retain stored composition``() =
        let result = OptionDefaults.check """
let invoke f x = f x
type Defaults = { choose: int<m> -> int<m> option -> int<m> }
[<EntryPoint>]
let main _ =
    let choose = Option.defaultValue
    let distance = choose 3<m> None
    let elapsed = choose 2<s> (Some 4<s>)
    let enabled = choose false (Some true)
    let surface = { choose = Option.defaultValue<int<m>> }
    let stored = surface.choose 8<m>
    if distance = 3<m> && elapsed = 4<s> && enabled && invoke stored None = 8<m> then 0 else 1
"""
        let aliases = result.Graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.Binding (name, _, _, _) -> name.StartsWith("choose__mono")
            | _ -> false) |> Seq.toList
        Assert.Equal(3, aliases.Length)

    [<Fact>]
    member _.``Function payloads keep the two argument operation boundary``() =
        let result = OptionDefaults.check """
let fallback = fun (distance: int<m>) -> distance + 1<m>
let direct = Option.defaultValue fallback (Some (fun distance -> distance + 2<m>)) 3<m>
let explicit = Option.defaultValue<(int<m> -> int<m>)> fallback None 3<m>
let stored = Option.defaultValue fallback
let partial = stored None 4<m>
let bare = Option.defaultValue<(int<m> -> int<m>)>
let throughBare = bare fallback None 5<m>
let staged = Option.defaultValue (fun (x: int<m>) -> fun () -> x) None 6<m> ()
[<EntryPoint>]
let main _ = if direct = 5<m> && explicit = 4<m> && partial = 5<m> && throughBare = 6<m> && staged = 6<m> then 0 else 1
"""
        let measured = DimensionalCases.measuredInt DimensionalCases.metre
        for name in ["direct"; "explicit"; "partial"; "throughBare"; "staged"] do
            DimensionalCases.same measured (DimensionalCases.bindingType name result)
        let selectedCalls =
            result.Graph.Nodes.Values |> Seq.filter (fun node ->
                node.IsReachable &&
                match node.Kind with
                | SemanticKind.Application (callee, [_]) ->
                    match result.Graph.Nodes[callee].Kind with
                    | SemanticKind.IfThenElse _ -> true
                    | _ -> false
                | _ -> false) |> Seq.toList
        Assert.NotEmpty selectedCalls

    [<Fact>]
    member _.``Stored measured applications retain their ordinary participant obligations``() =
        let result = OptionDefaults.check """
let stored = Option.defaultValue 3<m>
let observed = stored (Some 4<m>)
[<EntryPoint>]
let main _ = if observed = 4<m> then 0 else 1
"""
        let graph = result.Graph
        let site = OptionDefaults.value "observed" result
        match site.Kind with
        | SemanticKind.Application (callee, arguments) ->
            let enrichment = Clef.Compiler.Nanopass.ObligationElaboration.elaborate graph
            let obligation = enrichment.NewNodes |> List.find (fun node ->
                node.Range = site.Range &&
                match node.Kind with
                | SemanticKind.Obligation { Body = ObligationBody.ApplicationDimensions _ } -> true
                | _ -> false)
            let edge = enrichment.NewEdges |> List.find (fun edge -> edge.Target = obligation.Id)
            for participant in site.Id :: callee :: arguments do
                Assert.Contains(participant, edge.Sources)
            match graph.Nodes[callee].Kind with
            | SemanticKind.VarRef (_, Some definition) -> Assert.Contains(definition, edge.Sources)
            | kind -> failwithf "Stored application lost its definition: %A" kind
        | kind -> failwithf "Expected a stored function application, got %A" kind
