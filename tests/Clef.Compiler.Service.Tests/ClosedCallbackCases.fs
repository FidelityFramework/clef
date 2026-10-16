namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeService
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.PSGSaturation.SemanticGraph.CallbackDeclarations

module private ClosedCallbackCases =
    let declarations = """
module ClosedCallbacks
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Pointer of int | Void
type PassBy = | Value
type CallConv = | CDecl
type Transfer = | Borrowed
type ParameterInfo = { Name: string; Type: TypeRef; PassBy: PassBy }
type FunctionDescriptor = { CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }
type CallbackDescriptor = { Record: string; Field: string; Signature: FunctionDescriptor }
type ClosedCallbackDescriptor = { Binding: string; Adapter: string; Record: string; Field: string }
type NativeEntry = { Invoke: FnPtr<int -> CHandle<unit> -> unit> }
let entryDescriptor: Expr<CallbackDescriptor> = <@ { Record = "NativeEntry"; Field = "Invoke"; Signature = { CName = "Test::message"; Parameters = [| { Name = "value"; Type = Integer (Signed, 32); PassBy = Value }; { Name = "data"; Type = Pointer 64; PassBy = Value } |]; ReturnType = Void; CallingConvention = CDecl; OwnershipTransfer = Borrowed } } @>
let private adapter (handler: int -> unit) (value: int) (_data: CHandle<unit>) : unit = handler value
let private makeEntry (handler: int -> unit) : NativeEntry = NativeDefault.zeroed ()
let closedDescriptor: Expr<ClosedCallbackDescriptor> = <@ { Binding = "ClosedCallbacks.makeEntry"; Adapter = "ClosedCallbacks.adapter"; Record = "NativeEntry"; Field = "Invoke" } @>
let inline listener handler = makeEntry handler
"""
    let check (source: string) =
        let marker = "let inline listener handler = makeEntry handler\n"
        let split = source.IndexOf(marker) + marker.Length
        let library = source.Substring(0, split)
        let application = "module Application\nopen ClosedCallbacks\n" + source.Substring(split)
        let parsed =
            [library, "closed-bindings.clef"; application, "closed-application.clef"]
            |> List.map (fun (text, path) ->
                match parseStringWithDefaults text path with
                | ParseSuccess input -> input
                | ParseError errors -> failwithf "Parse failed: %A" errors)
        checkParsedInputs parsed
    let entries graph = (read graph).Callbacks
    let handlerReferences (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.choose (fun node ->
            if not node.IsReachable then None else
            match node.Kind with
            | SemanticKind.VarRef (_, Some target) ->
                match graph.Nodes[target].Kind with
                | SemanticKind.Binding (name, _, _, _) when name.StartsWith("handler") -> Some name
                | _ -> None
            | _ -> None) |> Set.ofSeq

    // This source fixture stipulates a receiving C contract. It executes no C.
    let receivingCheckUsing (metadata:(string*string) list) wrapper transform =
        let source =
            """
module ReceivingCallback
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Void | Entry of string
type PassBy = | Value
type CallConv = | CDecl
type Transfer = | Undeclared
type ParameterInfo = { Name: string; Type: TypeRef; PassBy: PassBy }
type FunctionDescriptor = { CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }
type EntrySignature = { Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv }
type ExternalExecutionHypothesis = { Identity: string; Version: string; Source: string }
type ScopedCallbackDescriptor = { Binding: string; Parameter: string }
type CallbackInvocationContract = { Binding: string; Parameter: int; Signature: EntrySignature; Hypothesis: ExternalExecutionHypothesis; Scope: string }
[<FidelityExtern("c", "consume_callback")>]
let private receive (callback: FnPtr<int -> int>) : unit = NativeDefault.zeroed ()
let receiveDescriptor: Expr<FunctionDescriptor> = <@ { CName = "consume_callback"; Parameters = [| { Name = "callback"; Type = Entry "ReceivingCallback.invocation"; PassBy = Value } |]; ReturnType = Void; CallingConvention = CDecl; OwnershipTransfer = Undeclared } @>
let scope: Expr<ScopedCallbackDescriptor> = <@ { Binding = "ReceivingCallback.receive"; Parameter = "callback" } @>
let invocation: Expr<CallbackInvocationContract> = <@ { Binding = "ReceivingCallback.receive"; Parameter = 0; Signature = { Parameters = [| { Name = "arg0"; Type = Integer (Signed, 64); PassBy = Value } |]; ReturnType = Integer (Signed, 64); CallingConvention = CDecl }; Hypothesis = { Identity = "receiving-test"; Version = "v1"; Source = "declared-source-fixture" }; Scope = "ReceivingCallback.scope" } @>
let callback (_unused: int) = 7
[<EntryPoint>]
let main _ =
    receive (FnPtr.ofFunction callback)
    0
"""

        let source =
            if wrapper then
                let record =
                    "type NativeRecord = { Handler: FnPtr<int -> int> }\nlet receiveRecord (callback: NativeRecord) = receive callback.Handler\nlet callback (_unused: int) = 7"

                let wrapped = source.Replace("let callback (_unused: int) = 7", record)
                wrapped.Replace("    receive (FnPtr.ofFunction callback)", "    receiveRecord { Handler = FnPtr.ofFunction callback }")
            else
                source

        let source = transform source

        let parse source path =
            match parseStringWithDefaults source path with
            | ParseSuccess input -> input
            | ParseError errors -> failwithf "Parse failed: %A" errors

        let platform = SourcePlatformFixture.platform

        let authority =
            SourcePlatformFixture.authority.Replace("Runtime = \"freestanding\"", "Runtime = \"libc\"")

        let sourcePath path = if metadata.IsEmpty then path else System.IO.Path.GetFullPath path
        let ownedSources = if metadata.IsEmpty then Set.empty else [sourcePath "write-authority.clef";sourcePath "receiving-callback.clef"] |> Set.ofList

        let result =
            checkParsedInputsWithPlatformAndSources
                [
                    yield! metadata |> List.map(fun(path,text)->parse text path)
                    parse authority (sourcePath "write-authority.clef")
                    parse source (sourcePath "receiving-callback.clef")
                ]
                (Some platform)
                ownedSources

        result

    let receivingCheckWith wrapper transform = receivingCheckUsing [] wrapper transform

    let receivingGraphWith wrapper =
        let result = receivingCheckWith wrapper id
        DimensionalCases.noErrors result
        result.Graph

    let pairSource callback (source: string) =
        source
            .Replace("FnPtr<int -> int>", "FnPtr<int -> int -> int>")
            .Replace("Parameters = [| { Name = \"arg0\"; Type = Integer (Signed, 64); PassBy = Value } |]", "Parameters = [| { Name = \"arg0\"; Type = Integer (Signed, 64); PassBy = Value }; { Name = \"arg1\"; Type = Integer (Signed, 64); PassBy = Value } |]")
            .Replace("let callback (_unused: int) = 7", callback)

    let receivingPairGraph useSecond =
        let callback = if useSecond then "let callback (_first: int) (second: int) = second" else "let callback (_first: int) (_second: int) = 7"
        let result = receivingCheckWith false (pairSource callback)
        DimensionalCases.noErrors result
        result.Graph

    let receivingUnitGraph mixed =
        let result =
            receivingCheckWith true (fun source ->
                let source =
                    (pairSource "let callback (_first: int) (_second: int) : unit =\n    let marker = 7\n    ()" source)
                        .Replace("FnPtr<int -> int -> int>", "FnPtr<int -> int -> unit>")
                        .Replace("ReturnType = Integer (Signed, 64); CallingConvention", "ReturnType = Void; CallingConvention")

                if mixed then
                    source
                        .Replace("{ Name = \"arg0\"; Type = Integer (Signed, 64)", "{ Name = \"arg0\"; Type = Integer (Signed, 32)")
                        .Replace("{ Name = \"arg1\"; Type = Integer (Signed, 64)", "{ Name = \"arg1\"; Type = Integer (Unsigned, 64)")
                else
                    source)

        DimensionalCases.noErrors result
        result.Graph

    let zeroSource signature callback (source: string) =
        source
                .Replace("FnPtr<int -> int>", "FnPtr<" + signature + ">")
                .Replace("type EntrySignature =", "type CallbackDescriptor = { Record: string; Field: string; Signature: FunctionDescriptor }\ntype EntrySignature =")
                .Replace("let receiveRecord (callback: NativeRecord)", "let legacyEntry: Expr<CallbackDescriptor> = <@ { Record = \"NativeRecord\"; Field = \"Handler\"; Signature = { CName = \"callback\"; Parameters = [||]; ReturnType = Void; CallingConvention = CDecl; OwnershipTransfer = Undeclared } } @>\nlet receiveRecord (callback: NativeRecord)")
                .Replace("Parameters = [| { Name = \"arg0\"; Type = Integer (Signed, 64); PassBy = Value } |]", "Parameters = [||]")
                .Replace("ReturnType = Integer (Signed, 64); CallingConvention", "ReturnType = Void; CallingConvention")
                .Replace("let callback (_unused: int) = 7", callback)

    let receivingZeroCheckWith signature callback =
        receivingCheckWith true (zeroSource signature callback)

    let receivingZeroCheck callback =
        receivingZeroCheckWith "unit -> unit" callback

    let receivingProcessCheckWith transform =
        receivingCheckWith true (fun source ->
            (zeroSource "unit -> unit" "let callback (u: unit) : unit = u" source)
                .Replace("type ScopedCallbackDescriptor = { Binding: string; Parameter: string }",
                         "type ScopedCallbackDescriptor = { Binding: string; Parameter: string }\ntype ProcessExitCallbackDescriptor = { Binding: string; Parameter: string; ExitBinding: string option; SuccessStatus: int }")
                .Replace("let private receive (callback: FnPtr<unit -> unit>) : unit", "let private receive (callback: FnPtr<unit -> unit>) : int")
                .Replace("ReturnType = Void; CallingConvention = CDecl; OwnershipTransfer = Undeclared } @>\nlet scope:",
                         "ReturnType = Integer (Signed, 32); CallingConvention = CDecl; OwnershipTransfer = Undeclared } @>\nlet scope:")
                .Replace("let scope: Expr<ScopedCallbackDescriptor> = <@ { Binding = \"ReceivingCallback.receive\"; Parameter = \"callback\" } @>",
                         "let scope: Expr<ProcessExitCallbackDescriptor> = <@ { Binding = \"ReceivingCallback.receive\"; Parameter = \"callback\"; ExitBinding = None; SuccessStatus = 0 } @>")
            |> transform)

    let receivingGraph () = receivingGraphWith false
    let receivingWrapperGraph () = receivingGraphWith true

    let optionalCheckUsing metadata present alias transform =
        receivingCheckUsing metadata false (fun source ->
            let actual = if present then "Some (FnPtr.ofFunction callback)" else "None"
            let invocation =
                if alias then "    let selected: option<FnPtr<int -> int>> = " + actual + "\n    receive selected"
                else "    receive (" + actual + ")"
            source.Replace("let private receive (callback: FnPtr<int -> int>)", "let private receive (callback: option<FnPtr<int -> int>>)")
                  .Replace("    receive (FnPtr.ofFunction callback)", invocation)
            |> transform)

    let optionalCheck present alias transform = optionalCheckUsing [] present alias transform

    // The real metadata vocabulary retains unreachable host-width diagnostics.
    // Use the same blocking predicate as ProjectChecker, then assert the issued path below.
    let absenceNoErrors result =
        if Clef.Compiler.NativeService.hasErrors result then failwithf "Unexpected blocking errors: %A" result.Diagnostics

    let absenceDeclaration = "let absence: Expr<BAREWire.Descriptors.CallbackAbsenceContract> = <@ { BAREWire.Descriptors.CallbackAbsenceContract.Binding = \"ReceivingCallback.receive\"; Parameter = 0; Hypothesis = { BAREWire.Descriptors.ExternalExecutionHypothesis.Identity = \"absence-test\"; Version = \"v1\"; Source = \"absence-source\" } } @>"

    let absenceCheck present alias transform =
        let bare = System.IO.Path.GetFullPath(System.IO.Path.Combine(__SOURCE_DIRECTORY__,"..","..","..","BAREWire","src"))
        let metadata=["Hardware/Descriptors.fs";"Descriptors/Bindings.fs"] |> List.map(fun relative -> let path=System.IO.Path.Combine(bare,relative) in path,System.IO.File.ReadAllText path)
        optionalCheckUsing metadata present alias (fun source ->
            source.Replace("let callback (_unused: int) = 7",absenceDeclaration+"\nlet callback (_unused: int) = 7") |> transform)

    let private withSecondReceiver (source:string) =
        let declarations=source.Split('\n') |> Array.filter(fun line->line.StartsWith("let private receive ") || line.StartsWith("let receiveDescriptor:") || line.StartsWith("let scope") || line.StartsWith("let invocation")) |> String.concat "\n"
        let other=declarations.Replace("let private receive ","let private secondReceiver ").Replace("let receiveDescriptor:","let secondReceiverDescriptor:")
                              .Replace("let scope","let secondScope").Replace("let invocation","let secondInvocation")
                              .Replace("ReceivingCallback.receive","ReceivingCallback.secondReceiver").Replace("ReceivingCallback.scope","ReceivingCallback.secondScope").Replace("ReceivingCallback.invocation","ReceivingCallback.secondInvocation")
                              .Replace("consume_callback","consume_other")
        source.Replace("let callback (_unused: int) = 7","[<FidelityExtern(\"c\", \"consume_other\")>]\n"+other+"\nlet callback (_unused: int) = 7")

    let mixedFormalCheck noneFirst transform =
        absenceCheck true false (fun source ->
            let present="    receive (Some (FnPtr.ofFunction callback))"
            let absent="    receive None"
            source.Replace(present,if noneFirst then absent+"\n"+present else present+"\n"+absent)
            |> withSecondReceiver |> transform)

    let mixedAbsenceCheck otherSite transform =
        absenceCheck true false (fun source ->
            let call="    receive (Some (FnPtr.ofFunction callback))"
            let source =
                let scope=source.Split('\n') |> Array.find(fun line->line.StartsWith("let scope:"))
                let invocation=source.Split('\n') |> Array.find(fun line->line.StartsWith("let invocation:"))
                let extra=scope.Replace("let scope:","let scope2:").Replace("Parameter = \"callback\"","Parameter = \"other\"")+"\n"+
                          invocation.Replace("let invocation:","let invocation2:").Replace("Parameter = 0","Parameter = 1").Replace("ReceivingCallback.scope\"","ReceivingCallback.scope2\"").Replace("ReturnType = Integer (Signed, 64)","ReturnType = Void")
                source.Replace("(callback: option<FnPtr<int -> int>>) : unit","(callback: option<FnPtr<int -> int>>) (other: option<FnPtr<int -> unit>>) : unit")
                      .Replace("Entry \"ReceivingCallback.invocation\"; PassBy = Value } |]","Entry \"ReceivingCallback.invocation\"; PassBy = Value }; { Name = \"other\"; Type = Entry \"ReceivingCallback.invocation2\"; PassBy = Value } |]")
                      .Replace(absenceDeclaration,absenceDeclaration.Replace("Parameter = 0","Parameter = 1"))
                      .Replace("let callback (_unused: int) = 7",extra+"\nlet callback (_unused: int) = 7")
                      .Replace(call,call+" None")
            let source = if otherSite then source.Replace(call+" None","    let selected: option<FnPtr<int -> int>> = Some (FnPtr.ofFunction callback)\n    let absent: option<FnPtr<int -> unit>> = None\n    receive selected absent\n    receive selected absent") else source
            source |> withSecondReceiver |> transform)

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "ClosedCallbacks")>]
type ClosedCallbackTests() =
    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Optional mixed formal retains per-application Some and None accounts``(noneFirst) =
        let result=ClosedCallbackCases.mixedFormalCheck noneFirst id
        ClosedCallbackCases.absenceNoErrors result
        let graph=result.Graph
        let claims=graph.Nodes |> Map.toList |> List.choose(fun(id,node)->
            match node.Kind with
            | SemanticKind.Obligation info ->
                match info.Body with
                | ObligationBody.OptionalEntryArgumentConversion model -> Some(id,info,model.Call,model.Parameter,model.Actual,model.Construction,true)
                | ObligationBody.OptionalEntryAbsenceArgumentConversion model -> Some(id,info,model.Call,model.Parameter,model.Actual,model.Construction,false)
                | _ -> None
            | _ -> None)
        Assert.Equal(2,claims.Length)
        Assert.Equal(2,claims |> List.map(fun(_,info,_,_,_,_,_)->info.Id) |> List.distinct |> List.length)
        Assert.Equal(2,claims |> List.map(fun(_,_,call,_,_,_,_)->call) |> List.distinct |> List.length)
        Assert.Equal(2,claims |> List.map(fun(_,_,_,_,actual,_,_)->actual) |> List.distinct |> List.length)
        let calls=Clef.Compiler.Baker.Recipes.ProofDispatchRecipes.boundaryCalls graph
        let selectedCalls=claims |> List.map(fun(_,_,site,_,_,_,_)->calls |> List.find(fun call->call.Site=site))
        let formal=selectedCalls |> List.map(fun call->call.Arguments[0].Formal) |> List.distinct |> Assert.Single
        let declarations=graph.Edges |> List.choose(fun edge->match edge.Role with EdgeRole.BoundaryDeclaration declaration->Some declaration | _->None)
        Assert.Contains(declarations,fun declaration->List.contains formal declaration.Formals)
        let origins=Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolveCallableBranches graph
        Assert.False(origins.Aggregates.ContainsKey formal)
        Assert.False(graph.Codata.Value.CallableAggregateValues.ContainsKey formal)
        let boundary=Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission.project graph |> Result.defaultWith(failwithf "%A")
        let absence=boundary.CallbackAbsences.Values |> Assert.Single
        for id,info,site,ordinal,actual,construction,present in claims do
            Assert.Equal(0,ordinal)
            let call=selectedCalls |> List.find(fun call->call.Site=site)
            Assert.Equal(actual,call.Arguments[ordinal].Actual)
            Assert.Contains(formal,call.Participants)
            Assert.True(origins.Aggregates.ContainsKey actual)
            let account=Clef.Compiler.Baker.Ingredients.CallableAggregateAccounts.current graph actual |> Result.defaultWith failwith
            Assert.Contains(account.Sources,fun source->source.Node=construction)
            let support=Clef.Compiler.Baker.Recipes.BoundaryRecipes.optionalEntryClaimRows graph calls (id,info) |> Result.defaultWith failwith |> List.collect _.Sources
            Assert.Contains(actual,support)
            Assert.Contains(formal,support)
            Assert.Contains(construction,support)
            let otherActual=claims |> List.find(fun(other,_,_,_,_,_,_)->other<>id) |> fun(_,_,_,_,other,_,_)->other
            Assert.DoesNotContain(otherActual,support)
            if present then Assert.DoesNotContain(absence.Quote,support) else Assert.Contains(absence.Quote,support)
        let revision=Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph |> Result.defaultWith(failwithf "%A")
        Assert.Empty(Fidelity.PSG.Integrity.check revision)

    [<Theory>]
    [<InlineData("stale")>]
    [<InlineData("ordinal")>]
    [<InlineData("withdrawn")>]
    member _.``Optional mixed formal refuses changed per-application source authority``(shape:string) =
        let result=ClosedCallbackCases.mixedFormalCheck false id
        ClosedCallbackCases.absenceNoErrors result
        let graph=result.Graph
        let claims=graph.Nodes |> Map.toList |> List.choose(fun(id,node)->
            match node.Kind with
            | SemanticKind.Obligation info ->
                match info.Body with
                | ObligationBody.OptionalEntryArgumentConversion model -> Some(id,info,model.Actual,model.Construction)
                | ObligationBody.OptionalEntryAbsenceArgumentConversion model -> Some(id,info,model.Actual,model.Construction)
                | _ -> None
            | _ -> None)
        Assert.Equal(2,claims.Length)
        for id,info,actual,construction in claims do
            let changed,claim,reason=
                match shape with
                | "stale" ->
                    let source=graph.Nodes[construction]
                    let kind=match source.Kind with
                             | SemanticKind.UnionCase(name,ordinal,payload)->SemanticKind.UnionCase(name,1-ordinal,payload)
                             | SemanticKind.DUConstruct(name,ordinal,payload,representation)->SemanticKind.DUConstruct(name,1-ordinal,payload,representation)
                             | _->failwith "Original optional construction disappeared"
                    {graph with Nodes=graph.Nodes.Add(construction,{source with Kind=kind})},info,
                    "Callable aggregate source support changed after its dependency account was authored (CCS8414)."
                | "ordinal" ->
                    let body,reason=match info.Body with
                                    | ObligationBody.OptionalEntryArgumentConversion model -> ObligationBody.OptionalEntryArgumentConversion {model with Parameter=1},"The optional-entry conversion claim lost its exact current Some source plan."
                                    | ObligationBody.OptionalEntryAbsenceArgumentConversion model -> ObligationBody.OptionalEntryAbsenceArgumentConversion {model with Parameter=1},"The optional-entry absence conversion claim lost its exact current quoted promise or None source plan."
                                    | _->failwith "Original conversion body disappeared"
                    graph,{info with Body=body},reason
                | _ ->
                    let facts=graph.Codata.Value
                    {graph with Codata=lazy {facts with CallableAggregateDependencies=facts.CallableAggregateDependencies.Remove actual}},info,
                    "An optional-entry source account lacks its exact current aggregate slots."
            let calls=Clef.Compiler.Baker.Recipes.ProofDispatchRecipes.boundaryCalls changed
            match Clef.Compiler.Baker.Recipes.BoundaryRecipes.optionalEntryClaimRows changed calls (id,claim) with
            | Result.Error actualReason -> Assert.Equal(reason,actualReason)
            | Ok _ -> failwithf "Changed %s authority retained its original per-application claim" shape
            for otherId,otherInfo,_,_ in claims |> List.filter(fun(other,_,_,_)->other<>id) do
                Clef.Compiler.Baker.Recipes.BoundaryRecipes.optionalEntryClaimRows changed calls (otherId,otherInfo)
                |> Result.defaultWith(failwithf "Changed %s authority invalidated the other original actual: %s" shape)
                |> ignore

    [<Fact>]
    member _.``Optional mixed formal keeps ordinary aggregate origins outside foreign exclusion``() =
        let result=ClosedCallbackCases.mixedFormalCheck false (fun source->
            source.Replace("    receive ","    relay ")
                  .Replace("[<EntryPoint>]","let relay (value: option<FnPtr<int -> int>>) = receive value\n[<EntryPoint>]"))
        let graph=result.Graph
        let foreignFormals=graph.Edges |> List.collect(fun edge->match edge.Role with EdgeRole.BoundaryDeclaration declaration->declaration.Formals | _->[]) |> Set.ofList
        let ordinary=graph.Nodes.Values |> Seq.filter(fun node->
            match node.Kind with
            | SemanticKind.PatternBinding _ when not(foreignFormals.Contains node.Id)->
                Clef.Compiler.Baker.Ingredients.CallableAggregateTypes.slots graph node.Type |> List.isEmpty |> not
            | _->false) |> Assert.Single
        let origins=Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolveCallableBranches graph
        Assert.True(origins.Aggregates.ContainsKey ordinary.Id)
        Assert.Equal(2,origins.Aggregates[ordinary.Id].Alternatives.Length)
        let actuals=origins.ParameterInputs[ordinary.Id] |> List.map snd |> List.distinct
        Assert.Equal(2,actuals.Length)
        for actual in actuals do Assert.True(origins.Aggregates.ContainsKey actual)
        let work=Clef.Compiler.Baker.Recipes.CallableAggregateRecipes.prepareWork origins graph
        Assert.Contains(work,fun group->group.Rows |> List.exists(fun(site,_,_)->site=ordinary.Id))
        for formal in foreignFormals do
            match graph.Nodes[formal].Kind with
            | SemanticKind.PatternBinding _->Assert.False(origins.Aggregates.ContainsKey formal)
            | _->()

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Optional mixed formal without absence promise keeps None Pending``(noneFirst) =
        let result=ClosedCallbackCases.mixedFormalCheck noneFirst (fun source->source.Replace(ClosedCallbackCases.absenceDeclaration,""))
        ClosedCallbackCases.absenceNoErrors result
        let revision=Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish result.Graph |> Result.defaultWith(failwithf "%A")
        Assert.Single(revision.CurrentClaims.Values |> Seq.filter(fun info->match info.Body with Fidelity.PSG.ObligationBody.OptionalEntryArgumentConversion _->true | _->false)) |> ignore
        let pending=revision.CurrentClaims.Values |> Seq.filter(fun info->info.Kind.StartsWith("foreign-optional-entry-conversion-") && (match info.Body with Fidelity.PSG.ObligationBody.Pending _->true | _->false)) |> Assert.Single
        match pending.Body with
        | Fidelity.PSG.ObligationBody.Pending reasons->Assert.Equal<string list>(["Selected-target optional-entry conversion and the foreign nullable-acceptance premise remain Pending."],reasons)
        | _->failwith "Missing absence promise was silently admitted"

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Optional absence content never enters Some support at same call or ordinal``(otherSite) =
        let result=ClosedCallbackCases.mixedAbsenceCheck otherSite id
        ClosedCallbackCases.absenceNoErrors result
        let graph=result.Graph
        let claims=graph.Nodes |> Map.toList |> List.choose(fun(id,node)->match node.Kind with SemanticKind.Obligation info when info.Kind.StartsWith("foreign-optional-entry-conversion-")->Some(id,info) | _->None)
        let someClaims=claims |> List.filter(fun(_,info)->match info.Body with ObligationBody.OptionalEntryArgumentConversion _->true | _->false)
        let noneClaims=claims |> List.filter(fun(_,info)->match info.Body with ObligationBody.OptionalEntryAbsenceArgumentConversion _->true | _->false)
        Assert.Equal((if otherSite then 2 else 1),someClaims.Length)
        Assert.Equal((if otherSite then 2 else 1),noneClaims.Length)
        let calls=Clef.Compiler.Baker.Recipes.ProofDispatchRecipes.boundaryCalls graph
        let boundary=Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission.project graph |> Result.defaultWith(failwithf "%A")
        let absence=boundary.CallbackAbsences.Values |> Assert.Single
        let content=absence.Inputs |> List.find(fun(role,_)->role=CallbackAbsenceInputRole.Binding) |> snd |> List.last
        let changed={graph with Nodes=graph.Nodes.Add(content,{graph.Nodes[content] with Kind=SemanticKind.Literal(NativeLiteral.String "ReceivingCallback.secondReceiver")})}
        for someId,someInfo in someClaims do
            let before=Clef.Compiler.Baker.Recipes.BoundaryRecipes.optionalEntryClaimRows graph calls (someId,someInfo) |> Result.defaultWith failwith |> List.map _.Sources
            for _,path in absence.Inputs do for id in path do Assert.DoesNotContain(id,List.concat before)
            let after=Clef.Compiler.Baker.Recipes.BoundaryRecipes.optionalEntryClaimRows changed calls (someId,someInfo) |> Result.defaultWith failwith |> List.map _.Sources
            Assert.Equal<NodeId list list>(before,after)
            let oldProposition=Clef.Compiler.Nanopass.ObligationDischarge.smtLib [someInfo]
            let changedInfo=match changed.Nodes[someId].Kind with SemanticKind.Obligation info->info | _->failwith "Some citizen disappeared"
            Assert.Equal(someInfo,changedInfo)
            Assert.Equal(oldProposition,Clef.Compiler.Nanopass.ObligationDischarge.smtLib [changedInfo])
            let model=match someInfo.Body with ObligationBody.OptionalEntryArgumentConversion model->model | _->failwith "Missing Some body"
            let facts=graph.Codata.Value
            let account=facts.CallableAggregateDependencies[model.Actual]
            Assert.Contains(account.Sources,fun source->source.Node=model.Construction)
            let selected=calls |> List.find(fun call->call.Site=model.Call) |> _.Arguments |> List.item model.Parameter |> _.OptionalEntry |> Option.get
            Assert.Contains(model.Payload,selected.Transport)
            Assert.Contains(model.Formation,selected.Transport)
            let source=List.head account.Sources
            let stale={graph with Codata=lazy {facts with CallableAggregateDependencies=facts.CallableAggregateDependencies.Add(model.Actual,{account with Sources={source with Anchors="changed-Some-source"::source.Anchors}::List.tail account.Sources})}}
            match Clef.Compiler.Baker.Recipes.BoundaryRecipes.optionalEntryClaimRows stale calls (someId,someInfo) with
            | Result.Error reason -> Assert.Equal("Callable aggregate source support changed after its dependency account was authored (CCS8414).",reason)
            | Ok _ -> failwith "A changed relevant Some account retained a valid claim"
        for noneId,noneInfo in noneClaims do
            Assert.True(Clef.Compiler.Baker.Recipes.BoundaryRecipes.optionalEntryClaimRows changed calls (noneId,noneInfo) |> Result.isError)
            let dispatch=Clef.Compiler.Baker.Recipes.ProofDispatchRecipes.materialize changed |> Result.defaultWith(failwithf "%A")
            match dispatch.Query with
            | Result.Error failures -> Assert.Contains(failures,fun(id,_)->id=noneId)
            | _ -> failwith "Stale absence content became solver-ready"

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Optional absence real BARE quote retains None plan and exact public account``(alias) =
        let result=ClosedCallbackCases.absenceCheck false alias id
        ClosedCallbackCases.absenceNoErrors result
        let graph=result.Graph
        let declared=graph.Nodes.Values |> Seq.choose(fun node -> match node.Kind with SemanticKind.Binding("absence",_,_,_) -> Some node | _->None) |> Assert.Single
        let quoted,_=Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.valuePath graph (List.last declared.Children) |> Option.get
        let expectedFile=System.IO.Path.GetFullPath(System.IO.Path.Combine(__SOURCE_DIRECTORY__,"..","..","..","BAREWire","src","Descriptors","Bindings.fs"))
        let identity=match Clef.Compiler.NativeTypedTree.UnionFind.applySubst quoted.Type with NativeType.TApp(constructor,[])->NominalTypeIdentity.ofConstructor constructor | _->failwith "Absence annotation lost its nominal constructor"
        let canonical=Clef.Compiler.PSGSaturation.SemanticGraph.RecordInstances.definitions graph |> Map.find identity
        Assert.Equal(expectedFile,canonical.Range.File)
        Assert.Equal(Clef.Compiler.NativeTypedTree.TypeIdentities.ofType canonical.Type,Clef.Compiler.NativeTypedTree.TypeIdentities.ofType quoted.Type)
        let revision=Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph |> Result.defaultWith(failwithf "%A")
        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let absence=revision.Emission.Boundary.CallbackAbsences.Values |> Assert.Single
        Assert.Equal("absence-test",absence.Contract.Hypothesis.Identity)
        let citizen,claim=revision.CurrentClaims |> Map.toList |> List.filter(fun(_,claim)->match claim.Body with Fidelity.PSG.ObligationBody.OptionalEntryAbsenceArgumentConversion _->true | _->false) |> Assert.Single
        let model=match claim.Body with Fidelity.PSG.ObligationBody.OptionalEntryAbsenceArgumentConversion model->model | _->failwith "Missing None plan"
        Assert.Equal(0,model.SourceCase)
        Assert.Equal(absence.Quote,model.Absence)
        Assert.Contains(claim.Id,revision.ObligationQuery)
        let limits:Fidelity.PSG.Binary.Limits={MaxBytes=16000000;MaxCollectionLength=100000;MaxDepth=128;MaxStringBytes=1000000;MaxBigIntegerBytes=4096;MaxValues=10000000}
        let bytes=Fidelity.PSG.Binary.encode limits revision |> Result.defaultWith(failwithf "%A")
        let copy=Fidelity.PSG.Binary.decode limits bytes |> Result.defaultWith(failwithf "%A")
        Assert.Equal(claim,copy.CurrentClaims[citizen])
        let call=revision.Emission.Boundary.Calls[model.Call]
        let promiseSource=absence.Inputs |> List.find(fun(role,_)->role=Fidelity.PSG.CallbackAbsenceInputRole.HypothesisSource) |> snd |> List.last
        for changed in [ {revision with Emission={revision.Emission with Boundary={revision.Emission.Boundary with CallbackAbsences=Map.empty}}}
                         {revision with Emission={revision.Emission with Boundary={revision.Emission.Boundary with Calls=revision.Emission.Boundary.Calls.Add(call.Site,{call with Participants=call.Participants.Remove promiseSource})}}}
                         {revision with Emission={revision.Emission with Boundary={revision.Emission.Boundary with CallbackAbsences=revision.Emission.Boundary.CallbackAbsences.Add(absence.Quote,{absence with Contract={absence.Contract with Hypothesis={absence.Contract.Hypothesis with Version="changed"}}})}}} ] do
            Assert.Contains(Fidelity.PSG.Integrity.check changed,fun violation->violation.Part="Emission.Boundary.Calls.OptionalEntry.Obligation" || violation.Part="Emission.Boundary.CallbackAbsences")
        Assert.True(Fidelity.PSG.OptionalEntryArgumentProof.projectAbsence model |> Result.isOk)

    [<Theory>]
    [<InlineData("same-hypothesis","distinct from activation")>]
    [<InlineData("nonnull-formal","nonnull entry formal or contract")>]
    [<InlineData("receiver","exact current receiving invocation")>]
    [<InlineData("ordinal","exact current receiving invocation")>]
    [<InlineData("mutable","immutable quoted content paths")>]
    [<InlineData("duplicate","declared twice")>]
    [<InlineData("unquoted","one immutable quote")>]
    member _.``Optional absence handwritten quote independently refuses conflicting promise``(shape:string,reason:string) =
        let result=ClosedCallbackCases.absenceCheck false false (fun source ->
            match shape with
            | "same-hypothesis" -> source.Replace("Identity = \"absence-test\"","Identity = \"receiving-test\"")
            | "nonnull-formal" -> source.Replace("callback: option<FnPtr<int -> int>>","callback: FnPtr<int -> int>")
            | "receiver" -> source.Replace("CallbackAbsenceContract.Binding = \"ReceivingCallback.receive\"","CallbackAbsenceContract.Binding = \"ReceivingCallback.missing\"")
            | "ordinal" -> source.Replace("CallbackAbsenceContract.Binding = \"ReceivingCallback.receive\"; Parameter = 0","CallbackAbsenceContract.Binding = \"ReceivingCallback.receive\"; Parameter = 1")
            | "mutable" -> source.Replace("let absence:","let mutable absence:")
            | "unquoted" -> source.Replace(ClosedCallbackCases.absenceDeclaration,ClosedCallbackCases.absenceDeclaration.Replace("Expr<BAREWire.Descriptors.CallbackAbsenceContract>","BAREWire.Descriptors.CallbackAbsenceContract").Replace("<@ ","").Replace(" @>",""))
            | _ -> source.Replace("let callback (_unused: int) = 7",ClosedCallbackCases.absenceDeclaration.Replace("let absence:","let secondAbsence:")+"\nlet callback (_unused: int) = 7"))
        Assert.Contains(result.Diagnostics,fun diagnostic->diagnostic.Message.Contains(reason))

    [<Fact>]
    member _.``Optional absence same leaf record never grants nominal promise``() =
        let result=ClosedCallbackCases.absenceCheck false false (fun source ->
            source.Replace(ClosedCallbackCases.absenceDeclaration,
                "type CallbackAbsenceContract = { Binding: string; Parameter: int; Hypothesis: BAREWire.Descriptors.ExternalExecutionHypothesis }\n"+
                ClosedCallbackCases.absenceDeclaration.Replace("BAREWire.Descriptors.CallbackAbsenceContract","CallbackAbsenceContract")))
        ClosedCallbackCases.absenceNoErrors result
        let revision=Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish result.Graph |> Result.defaultWith(failwithf "%A")
        Assert.Empty(revision.Emission.Boundary.CallbackAbsences)
        let optional=revision.CurrentClaims.Values |> Seq.filter(fun claim->claim.Kind.StartsWith("foreign-optional-entry-conversion-")) |> Assert.Single
        match optional.Body with
        | Fidelity.PSG.ObligationBody.Pending reasons -> Assert.Contains(reasons,fun reason->reason.Contains("foreign nullable-acceptance premise"))
        | _ -> failwith "A same-leaf record granted an absence promise"

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Optional absence stale account refuses dispatch with unchanged proposition``(withdrawn) =
        let result=ClosedCallbackCases.absenceCheck false false id
        ClosedCallbackCases.absenceNoErrors result
        let graph=result.Graph
        let citizen,claim=graph.Nodes |> Map.toList |> List.choose(fun(id,node)->match node.Kind with SemanticKind.Obligation info when (match info.Body with ObligationBody.OptionalEntryAbsenceArgumentConversion _->true | _->false)->Some(id,info) | _->None) |> Assert.Single
        let edges=graph.Edges |> List.choose(fun edge ->
            match edge.Role with
            | EdgeRole.BoundaryCallbackAbsence account ->
                if withdrawn then None
                else Some {edge with Role=EdgeRole.BoundaryCallbackAbsence {account with Contract={account.Contract with Hypothesis={account.Contract.Hypothesis with Version="stale"}}}}
            | _ -> Some edge)
        let changed={graph with Edges=edges}
        let calls=Clef.Compiler.Baker.Recipes.ProofDispatchRecipes.boundaryCalls changed
        match Clef.Compiler.Baker.Recipes.BoundaryRecipes.optionalEntryClaimRows changed calls (citizen,claim) with
        | Result.Error reason -> Assert.Equal("An absence conversion account is stale or withdrawn.",reason)
        | Ok _ -> failwith "A stale absence account retained its current claim rows"
        let dispatch=Clef.Compiler.Baker.Recipes.ProofDispatchRecipes.materialize changed |> Result.defaultWith(failwithf "%A")
        match dispatch.Query with
        | Result.Error failures -> Assert.Contains(failures,fun(id,reasons)->id=citizen && List.contains "An absence conversion account is stale or withdrawn." reasons)
        | _ -> failwith "A stale absence plan remained solver-ready"
        let held=match changed.Nodes[citizen].Kind with SemanticKind.Obligation info->info | _->failwith "The current citizen disappeared"
        Assert.Equal(Clef.Compiler.Nanopass.ObligationDischarge.smtLib [claim],Clef.Compiler.Nanopass.ObligationDischarge.smtLib [held])

    [<Fact>]
    member _.``Optional absence fresh quote rename retains nominal promise``() =
        let result=ClosedCallbackCases.absenceCheck false false (fun source->source.Replace("let absence:","let renamedPromise:"))
        ClosedCallbackCases.absenceNoErrors result
        let revision=Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish result.Graph |> Result.defaultWith(failwithf "%A")
        Assert.Single(revision.Emission.Boundary.CallbackAbsences) |> ignore
        revision.CurrentClaims.Values |> Seq.filter(fun claim->match claim.Body with Fidelity.PSG.ObligationBody.OptionalEntryAbsenceArgumentConversion _->true | _->false) |> Assert.Single |> ignore
        Assert.Empty(Fidelity.PSG.Integrity.check revision)

    [<Fact>]
    member _.``Optional absence immutable input binding retains exact content path``() =
        let result=ClosedCallbackCases.absenceCheck false false (fun source ->
            source.Replace(ClosedCallbackCases.absenceDeclaration,
                "let promisedReceiver = \"ReceivingCallback.receive\"\n"+ClosedCallbackCases.absenceDeclaration.Replace("CallbackAbsenceContract.Binding = \"ReceivingCallback.receive\"","CallbackAbsenceContract.Binding = promisedReceiver")))
        ClosedCallbackCases.absenceNoErrors result
        let revision=Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish result.Graph |> Result.defaultWith(failwithf "%A")
        let absence=revision.Emission.Boundary.CallbackAbsences.Values |> Assert.Single
        revision.CurrentClaims.Values |> Seq.filter(fun claim->match claim.Body with Fidelity.PSG.ObligationBody.OptionalEntryAbsenceArgumentConversion _->true | _->false) |> Assert.Single |> ignore
        let path=absence.Inputs |> List.find(fun(role,_)->role=Fidelity.PSG.CallbackAbsenceInputRole.Binding) |> snd
        Assert.Contains(path,fun id->absence.DeclarationFacts[id].Form="reference")
        Assert.Contains(path,fun id->absence.DeclarationFacts[id].Form="binding")
        Assert.Equal(absence.Record,List.last absence.SourcePath)
        Assert.Empty(Fidelity.PSG.Integrity.check revision)

    [<Theory>]
    [<InlineData(false, false)>]
    [<InlineData(true, false)>]
    [<InlineData(false, true)>]
    [<InlineData(true, true)>]
    member _.``Optional receiving entry retains explicit current source selection and Pending conversion``(present, alias) =
        let result = ClosedCallbackCases.optionalCheck present alias id
        DimensionalCases.noErrors result
        let graph = result.Graph
        let observations = read graph
        Assert.Empty observations.Receiving
        let selection = observations.OptionalReceiving |> Assert.Single
        Assert.Equal(present, selection.Payload.IsSome)
        Assert.Equal(present, selection.Receiving.IsSome)
        let boundary =
            match Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission.project graph with
            | Ok boundary -> boundary
            | Result.Error failures -> failwithf "Optional source boundary refused: %A" failures
        let call = boundary.Calls[selection.Call]
        let operand = call.Arguments |> Assert.Single
        let account = operand.OptionalEntry |> Option.get
        let expectedCase = if present then 1 else 0
        Assert.Equal(expectedCase, account.CaseOrdinal)
        match graph.Nodes[account.Construction].Kind with
        | SemanticKind.UnionCase(name, ordinal, payload)
        | SemanticKind.DUConstruct(name, ordinal, payload, _) ->
            Assert.Equal((if present then "Some" else "None"), name)
            Assert.Equal(expectedCase, ordinal)
            Assert.Equal(account.Payload, payload)
        | other -> failwithf "The optional construction is not the original literal Option case: %A" other
        match Clef.Compiler.NativeTypedTree.TypeIdentities.ofType graph.Nodes[account.Construction].Type with
        | Clef.Compiler.NativeTypedTree.NativeTypes.TypeIdentity.Application(constructor, [_]) ->
            Assert.Equal(Clef.Compiler.NativeTypedTree.TypeIdentities.constructor Types.optionTyCon, constructor)
        | other -> failwithf "The optional constructor lost its nominal source identity: %A" other
        let rec originalPath seen id =
            if Set.contains id seen then failwith "The source alias path repeats a node"
            elif id=account.Construction then [id]
            else
                let next =
                    match graph.Nodes[id].Kind, graph.Nodes[id].Children with
                    | SemanticKind.VarRef("selected", Some binding), [] -> binding
                    | SemanticKind.Binding("selected", false, false, _), [initializer] -> initializer
                    | SemanticKind.TypeAnnotation(inner, _), [child] when inner=child -> inner
                    | other -> failwithf "The fixture's alias is not its original immutable source edge: %A" other
                id :: originalPath (Set.add id seen) next
        let path = originalPath Set.empty operand.Actual
        let transports = graph.Codata.Value.CallableAggregateValues[operand.Actual] |> List.filter (fun row -> row.Operation=CallableAggregateOperation.Transport)
        if alias then
            Assert.NotEqual(operand.Actual, account.Construction)
            let transport = transports |> Assert.Single
            Assert.Equal<NodeId list>(List.tail path @ Option.toList account.Payload, transport.FormationInputs)
        else
            Assert.Equal(operand.Actual, account.Construction)
            Assert.Empty transports
        Assert.True(account.Transport = Set.ofList(path @ Option.toList account.Payload))
        Assert.Equal(selection.Operand, operand.Actual)
        Assert.Equal(selection.Construction, account.Construction)
        Assert.Equal(selection.CaseOrdinal, account.CaseOrdinal)
        Assert.Equal(selection.Payload, account.Payload)
        Assert.Equal(present, account.Formation.IsSome)
        Assert.Equal((if present then 1 else 0), boundary.ClosedEntries.Count)
        let invocation = boundary.CallbackInvocations.Values |> Assert.Single
        Assert.Equal(BoundaryScalar.Entry invocation.Identity, operand.Abi)
        Assert.Equal(BoundaryCallbackExtent.DuringCall, invocation.Extent)
        if present then
            let payload = account.Payload |> Option.get
            let entry = boundary.ClosedEntries.Values |> Assert.Single
            Assert.Equal(Some entry.Formation, account.Formation)
            Assert.Equal(payload, entry.Formation)
            match graph.Nodes[payload].Kind with
            | SemanticKind.Application(intrinsic, [_]) ->
                match graph.Nodes[intrinsic].Kind with
                | SemanticKind.Intrinsic info ->
                    Assert.Equal(IntrinsicModule.FnPtr, info.Module)
                    Assert.Equal("ofFunction", info.Operation)
                | other -> failwithf "The source payload callee is not FnPtr.ofFunction: %A" other
            | other -> failwithf "The source Some payload is not its ofFunction application: %A" other
        Assert.Contains(operand.Actual, call.Participants)
        Assert.Contains(operand.Formal, call.Participants)
        for id in account.Obligation :: account.Construction :: Set.toList account.Transport do Assert.Contains(id, call.Participants)
        let pending = graph.Nodes.Values |> Seq.choose (fun node -> match node.Kind with SemanticKind.Obligation claim when claim.Kind.StartsWith("foreign-optional-entry-conversion-") -> Some node.Id | _ -> None) |> Seq.toList
        Assert.Equal<NodeId>(account.Obligation, pending |> Assert.Single)
        match graph.Nodes[account.Obligation].Kind with
        | SemanticKind.Obligation claim ->
            Assert.Equal("foreign-optional-entry-conversion-0", claim.Kind)
            match claim.Body with
            | ObligationBody.Pending reasons when not present ->
                Assert.Contains(reasons, fun reason -> reason.Contains("conversion") && (present || reason.Contains("nullable-acceptance")))
            | ObligationBody.OptionalEntryArgumentConversion model when present ->
                Assert.Equal(call.Site, model.Call)
                Assert.Equal(0, model.Parameter)
                Assert.Equal(account.Construction, model.Construction)
                Assert.Equal(1, model.SourceCase)
                Assert.Equal(account.Payload, Some model.Payload)
                Assert.Equal(account.Formation, Some model.Formation)
            | body -> failwithf "Optional conversion was not Pending: %A" body
        | kind -> failwithf "Optional conversion lost its ledger citizen: %A" kind
        let sourceGroup = graph.Edges |> List.filter (fun edge -> edge.Target=account.Obligation && edge.Role=EdgeRole.Constrains) |> Assert.Single |> _.Sources
        for id in [call.Site;operand.Actual;account.Construction;invocation.Identity] @ Option.toList account.Formation do Assert.Contains(id, sourceGroup)
        let revision =
            Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph
            |> Result.defaultWith (fun errors -> failwithf "Optional revision publication refused: %A" errors)
        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let publicId = Clef.Compiler.Baker.Ingredients.PublishedFactRows.nodeId account.Obligation
        let publicClaim = revision.CurrentClaims[publicId]
        match publicClaim.Body with
        | Fidelity.PSG.ObligationBody.OptionalEntryArgumentConversion model ->
            let noneArm = model.Arms |> List.find (fun arm -> arm.CaseOrdinal=0)
            let someArm = model.Arms |> List.find (fun arm -> arm.CaseOrdinal=1)
            let mutants =
                [ {model with Arms=[someArm]}
                  {model with Arms=[noneArm;someArm;someArm]}
                  {model with Arms=[{noneArm with CaseOrdinal=1};{someArm with CaseOrdinal=0}]}
                  {model with Arms=[noneArm;{someArm with Formation=Some model.Construction}]}
                  {model with Arms=[{noneArm with Formation=Some model.Formation};someArm]} ]
            for mutant in mutants do
                let changedClaim = {publicClaim with Body=Fidelity.PSG.ObligationBody.OptionalEntryArgumentConversion mutant}
                let changed = {revision with CurrentClaims=revision.CurrentClaims.Add(publicId, changedClaim)
                                             Obligations=revision.Obligations |> List.map (fun claim -> if claim.Id=publicClaim.Id then changedClaim else claim)}
                Assert.Contains(Fidelity.PSG.Integrity.check changed, fun violation -> violation.Part="Emission.Boundary.Calls.OptionalEntry.Obligation")
        | _ -> ()
        let publicCall = revision.Emission.Boundary.Calls[Clef.Compiler.Baker.Ingredients.PublishedFactRows.nodeId call.Site]
        let transportNode = Clef.Compiler.Baker.Ingredients.PublishedFactRows.nodeId operand.Actual
        let changedCall = {publicCall with Participants=publicCall.Participants.Remove transportNode}
        let changedBoundary = {revision.Emission.Boundary with Calls=revision.Emission.Boundary.Calls.Add(publicCall.Site, changedCall)}
        let changedSupport = {revision with Emission={revision.Emission with Boundary=changedBoundary}}
        Assert.Contains(Fidelity.PSG.Integrity.check changedSupport, fun violation -> violation.Part="Emission.Boundary.Calls.OptionalEntry.Participants")
        match graph.Nodes[account.Obligation].Kind, publicClaim.Body with
        | SemanticKind.Obligation source, Fidelity.PSG.ObligationBody.Pending reasons ->
            Assert.Equal(source.Id, publicClaim.Id)
            match source.Body with
            | ObligationBody.Pending expected -> Assert.Equal<string list>(expected, reasons)
            | body -> failwithf "Optional source claim changed: %A" body
        | SemanticKind.Obligation source, Fidelity.PSG.ObligationBody.OptionalEntryArgumentConversion _ when present ->
            Assert.Equal(Clef.Compiler.Baker.Ingredients.PublishedFactRows.mapObligationInfo source, publicClaim)
        | other -> failwithf "Optional published claim changed: %A" other
        if present then Assert.Contains(publicClaim.Id, revision.ObligationQuery)
        else Assert.DoesNotContain(publicClaim.Id, revision.ObligationQuery)
        let sourceGroup = revision.ObligationSources[publicId] |> List.exactlyOne
        for groups in [[]; [List.rev sourceGroup]] do
            let changed = {revision with ObligationSources=revision.ObligationSources.Add(publicId, groups)}
            Assert.Contains(Fidelity.PSG.Integrity.check changed, fun violation ->
                violation.Part = "Emission.Boundary.Calls.OptionalEntry.Obligation")
        let limits : Fidelity.PSG.Binary.Limits =
            {MaxBytes=8*1024*1024; MaxCollectionLength=100000; MaxDepth=128
             MaxStringBytes=1024*1024; MaxBigIntegerBytes=4096; MaxValues=2000000}
        let bytes = Fidelity.PSG.Binary.encode limits revision |> Result.defaultWith (fun error -> failwithf "%A" error)
        let copy = Fidelity.PSG.Binary.decode limits bytes |> Result.defaultWith (fun error -> failwithf "%A" error)
        Assert.Empty(Fidelity.PSG.Integrity.check copy)
        Assert.Equal(publicClaim, copy.CurrentClaims[publicId])
        Assert.Equal<Fidelity.PSG.NodeId list list>(revision.ObligationSources[publicId], copy.ObligationSources[publicId])
        Assert.Equal<Fidelity.PSG.ObligationInfo list>(revision.Obligations, copy.Obligations)

    [<Fact>]
    member _.``Optional receiving entry rejects mutable alias transport``() =
        let result = ClosedCallbackCases.optionalCheck true true (fun source -> source.Replace("let selected:", "let mutable selected:"))
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Message.Contains("literal nominal Option constructor and immutable aliases"))

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Optional Some conversion refuses branch and function result alias transport``(functionResult) =
        let result = ClosedCallbackCases.optionalCheck true true (fun source ->
            if functionResult then
                source.Replace("[<EntryPoint>]", "let choose () = Some (FnPtr.ofFunction callback)\n[<EntryPoint>]")
                      .Replace("let selected: option<FnPtr<int -> int>> = Some (FnPtr.ofFunction callback)", "let selected: option<FnPtr<int -> int>> = choose ()")
            else source.Replace("let selected: option<FnPtr<int -> int>> = Some (FnPtr.ofFunction callback)",
                                "let selected: option<FnPtr<int -> int>> = if true then Some (FnPtr.ofFunction callback) else None"))
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Message.Contains("literal nominal Option constructor and immutable aliases"))
        Assert.Empty((read result.Graph).OptionalReceiving)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Optional Some conversion citizens stay unique across calls and native ordinals``(twoOrdinals) =
        let result = ClosedCallbackCases.optionalCheck true false (fun source ->
            let call = "    receive (Some (FnPtr.ofFunction callback))"
            if not twoOrdinals then source.Replace(call, "    let selected: option<FnPtr<int -> int>> = Some (FnPtr.ofFunction callback)\n    receive selected\n    receive selected")
            else
                let scope = source.Split('\n') |> Array.find (fun line -> line.StartsWith("let scope:"))
                let invocation = source.Split('\n') |> Array.find (fun line -> line.StartsWith("let invocation:"))
                let extra = scope.Replace("let scope:", "let scope2:").Replace("Parameter = \"callback\"", "Parameter = \"other\"") + "\n" +
                            invocation.Replace("let invocation:", "let invocation2:").Replace("Parameter = 0", "Parameter = 1").Replace("ReceivingCallback.scope\"", "ReceivingCallback.scope2\"").Replace("ReturnType = Integer (Signed, 64)", "ReturnType = Void")
                source.Replace("(callback: option<FnPtr<int -> int>>) : unit", "(callback: option<FnPtr<int -> int>>) (other: option<FnPtr<int -> unit>>) : unit")
                      .Replace("Entry \"ReceivingCallback.invocation\"; PassBy = Value } |]", "Entry \"ReceivingCallback.invocation\"; PassBy = Value }; { Name = \"other\"; Type = Entry \"ReceivingCallback.invocation2\"; PassBy = Value } |]")
                      .Replace("let callback (_unused: int) = 7", extra+"\nlet callback (_unused: int) = 7\nlet callback2 (_unused: int) : unit = ()")
                      .Replace(call, call+" (Some (FnPtr.ofFunction callback2))"))
        DimensionalCases.noErrors result
        let graph = result.Graph
        let claims = graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind with SemanticKind.Obligation ({Body=ObligationBody.OptionalEntryArgumentConversion model} as info) -> Some(node.Id,info,model) | _ -> None) |> Seq.toList
        Assert.Equal(2, claims.Length)
        Assert.Equal(2, claims |> List.map (fun (_, info, _) -> info.Id) |> List.distinct |> List.length)
        Assert.Equal((if twoOrdinals then 1 else 2), claims |> List.map (fun (_,_,model) -> model.Call) |> List.distinct |> List.length)
        Assert.Equal<int list>((if twoOrdinals then [0;1] else [0;0]), claims |> List.map (fun (_,_,model) -> model.Parameter) |> List.sort)
        for citizen, info, model in claims do
            Assert.True(Clef.Compiler.Baker.Recipes.BoundaryRecipes.optionalEntryClaimRows graph (Clef.Compiler.Baker.Recipes.ProofDispatchRecipes.boundaryCalls graph) (citizen,info) |> Result.isOk)
            let call = Clef.Compiler.Baker.Recipes.ProofDispatchRecipes.boundaryCalls graph |> List.find (fun call -> call.Site=model.Call)
            Assert.Equal(Some citizen, (List.item model.Parameter call.Arguments).OptionalEntry |> Option.map _.Obligation)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Optional receiving public adapter refuses absent contextual selection account``(present) =
        let result = ClosedCallbackCases.optionalCheck present false (fun source ->
            source.Replace("let callback (_unused: int) = 7",
                           "let call_optional (callback: option<FnPtr<int -> int>>) : unit = receive callback\nlet callback (_unused: int) = 7")
                  .Replace("    receive (", "    call_optional ("))
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Message.Contains("literal nominal Option constructor and immutable aliases"))
        Assert.Empty((read result.Graph).OptionalReceiving)
        Assert.Empty((read result.Graph).Receiving)

    [<Fact>]
    member _.``Optional receiving entry rejects user union with None Some case names``() =
        let result = ClosedCallbackCases.optionalCheck false false (fun source ->
            source.Replace("type Signedness =", "type Pretend<'T> = None | Some of 'T\ntype Signedness =")
                  .Replace("callback: option<FnPtr<int -> int>>", "callback: Pretend<FnPtr<int -> int>>"))
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Message.Contains("original nonnullable FnPtr formal"))

    [<Fact>]
    member _.``Optional receiving entry does not reuse record projection for Option field``() =
        let result = ClosedCallbackCases.receivingCheckWith true (fun source ->
            source.Replace("callback: FnPtr<int -> int>", "callback: option<FnPtr<int -> int>>")
                  .Replace("Handler: FnPtr<int -> int>", "Handler: option<FnPtr<int -> int>>")
                  .Replace("{ Handler = FnPtr.ofFunction callback }", "{ Handler = Some (FnPtr.ofFunction callback) }"))
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Message.Contains("literal nominal Option constructor and immutable aliases"))

    [<Fact>]
    member _.``Optional receiving entry refuses captured payload``() =
        let result = ClosedCallbackCases.optionalCheck true false (fun source ->
            source.Replace("    receive (Some (FnPtr.ofFunction callback))", "    let captured = 7\n    let local value = value + captured\n    receive (Some (FnPtr.ofFunction local))"))
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Message.Contains("closed"))
        Assert.Empty((read result.Graph).Receiving)

    [<Fact>]
    member _.``Optional receiving entry refuses process exit without registration``() =
        let result = ClosedCallbackCases.receivingProcessCheckWith (fun source ->
            source.Replace("let private receive (callback: FnPtr<unit -> unit>)", "let private receive (callback: option<FnPtr<unit -> unit>>)")
                  .Replace("receive callback.Handler", "receive None"))
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Message.Contains("process-exit optional callbacks are not admitted"))
        Assert.Empty((read result.Graph).OptionalReceiving)
        Assert.DoesNotContain((Clef.Compiler.PSGSaturation.SemanticGraph.ScopedDeclarations.read result.Graph).Activations.Values,
                              fun activation -> match activation.Extent with BoundaryCallbackExtent.ProcessExit _ -> true | _ -> false)

    [<Theory>]
    [<InlineData(false, false)>]
    [<InlineData(true, false)>]
    [<InlineData(false, true)>]
    [<InlineData(true, true)>]
    member _.``Optional receiving entry source account withdrawal refuses before publication``(present, alias) =
        let result = ClosedCallbackCases.optionalCheck present alias id
        DimensionalCases.noErrors result
        let graph = result.Graph
        let selection = (read graph).OptionalReceiving |> Assert.Single
        let facts = graph.Codata.Value
        let changed = {graph with Codata=lazy {facts with CallableAggregateDependencies=facts.CallableAggregateDependencies.Remove selection.Operand}}
        let call = Clef.Compiler.Baker.Recipes.ProofDispatchRecipes.boundaryCalls graph |> List.find (fun call -> call.Site=selection.Call)
        let claim = call.Arguments |> List.choose _.OptionalEntry |> List.exactlyOne |> _.Obligation
        match Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission.project changed with
        | Result.Error failures ->
            let failure = failures |> Assert.Single
            Assert.Equal(Some claim, failure.Occurrence)
            Assert.Equal("BoundaryEmission: The optional native callback lost its exact current per-use Pending conversion claim. An optional-entry source account lacks its exact current aggregate slots.", failure.Reason)
        | Ok _ -> failwith "Optional source selection survived account withdrawal"

    [<Fact>]
    member _.``Optional receiving Some to None source recheck withdraws payload activation and closed entry``() =
        for present in [true; false] do
            let result = ClosedCallbackCases.optionalCheck present false id
            DimensionalCases.noErrors result
            let graph = result.Graph
            let callback = graph.Nodes.Values |> Seq.filter (fun node -> match node.Kind with SemanticKind.Binding("callback", false, _, _) -> true | _ -> false) |> Assert.Single
            let lambda = callback.Children |> List.exactlyOne
            let formals = match graph.Nodes[lambda].Kind with SemanticKind.Lambda(formals, _, _, _, _) -> formals | other -> failwithf "Original callback declaration changed: %A" other
            let reading = read graph
            let selection = reading.OptionalReceiving |> Assert.Single
            let boundary =
                match Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission.project graph with
                | Ok boundary -> boundary
                | Result.Error failures -> failwithf "Optional source recheck refused: %A" failures
            Assert.Equal((if present then 1 else 0), boundary.ClosedEntries.Count)
            match present, selection.Receiving with
            | true, Some receiving -> Assert.Equal(lambda, receiving.Lambda)
            | false, None -> ()
            | other -> failwithf "Source payload activation survived the changed Option case: %A" other
            for _, _, formal in formals do Assert.Equal(present, reading.NumericBoundaries.ContainsKey formal)
            let call = boundary.Calls[selection.Call]
            let selected = call.Arguments |> List.choose _.OptionalEntry |> List.exactlyOne
            Assert.Equal((if present then 1 else 0), selected.CaseOrdinal)
            let pending = graph.Nodes.Values |> Seq.choose (fun node -> match node.Kind with SemanticKind.Obligation claim when claim.Kind.StartsWith("foreign-optional-entry-conversion-") -> Some(node.Id, claim) | _ -> None) |> Assert.Single
            let pendingId, claim = pending
            Assert.Equal(selected.Obligation, pendingId)
            match claim.Body with
            | ObligationBody.Pending [reason] when not present ->
                Assert.Equal("foreign-optional-entry-conversion-0", claim.Kind)
                Assert.Equal(not present, reason.Contains("nullable-acceptance"))
            | ObligationBody.OptionalEntryArgumentConversion model when present -> Assert.Equal(selected.Formation, Some model.Formation)
            | other -> failwithf "The current source conversion claim changed: %A" other

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Optional receiving Pending dispatch retains complete ledger and exact ready query``(present) =
        let result = ClosedCallbackCases.optionalCheck present false id
        DimensionalCases.noErrors result
        let graph = result.Graph
        let dispatch =
            match Clef.Compiler.Baker.Recipes.ProofDispatchRecipes.materialize graph with
            | Ok dispatch -> dispatch
            | Result.Error failures -> failwithf "Optional dispatch refused: %A" failures
        let pending = dispatch.Required |> List.filter (fun (_, info) -> info.Kind.StartsWith("foreign-optional-entry-conversion-"))
        let id, info = pending |> Assert.Single
        let boundary =
            match Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission.project graph with
            | Ok boundary -> boundary
            | Result.Error failures -> failwithf "Optional boundary refused: %A" failures
        Assert.True(Clef.Compiler.Baker.Recipes.ProofDispatchRecipes.optionalEntryPending graph boundary (id, info))
        let originalIds = Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.obligations graph |> List.map (fst >> _.Id) |> List.sort
        Assert.Equal<NodeId list>(originalIds, dispatch.Required |> List.map fst |> List.sort)
        let ready = dispatch.Required |> List.filter (fun (_, info) -> match info.Body with ObligationBody.Pending _ -> false | _ -> true)
        Assert.NotEmpty ready
        let query = dispatch.Query |> Result.defaultWith (fun _ -> failwith "Optional conversion still blocked the ready query")
        for _, claim in ready do Assert.Contains(claim.Id, query)
        if present then Assert.Contains(info.Id, query) else Assert.DoesNotContain(info.Id, query)
        Assert.Contains(id, dispatch.SourceGroups.Keys)
        let facts = graph.Codata.Value
        let scope = facts.WitnessLiveScope |> Option.defaultWith (fun () -> failwith "Optional source lost its live scope")
        let selected = facts.WitnessLiveRows |> Option.defaultWith (fun () -> failwith "Optional source lost its selected publication rows")
        match Clef.Compiler.Baker.Recipes.WitnessPublishedRowsRecipes.project graph scope selected dispatch with
        | Result.Error failures -> failwithf "Admitted optional Pending publication refused: %A" failures
        | Ok published ->
            let publicId = Clef.Compiler.Baker.Ingredients.PublishedFactRows.nodeId id
            let claim = published.CurrentClaims[publicId]
            Assert.Equal(info.Id, claim.Id)
            match info.Body, claim.Body with
            | ObligationBody.Pending reasons, Fidelity.PSG.ObligationBody.Pending publishedReasons ->
                Assert.Equal<string list>(reasons, publishedReasons)
                Assert.Contains(claim, published.Obligations)
                Assert.False(published.Nodes.ContainsKey publicId)
                let expectedGroups = dispatch.SourceGroups[id] |> List.map (List.map Clef.Compiler.Baker.Ingredients.PublishedFactRows.nodeId)
                Assert.Equal<Fidelity.PSG.NodeId list list>(expectedGroups, published.ObligationSources[publicId])
            | ObligationBody.OptionalEntryArgumentConversion _, Fidelity.PSG.ObligationBody.OptionalEntryArgumentConversion _ when present ->
                Assert.Equal(Clef.Compiler.Baker.Ingredients.PublishedFactRows.mapObligationInfo info, claim)
                Assert.Contains(claim, published.Obligations)
            | other -> failwithf "Optional Pending disappeared from the published ledger: %A" other
        if not present then Assert.Throws<System.InvalidOperationException>(fun () -> Clef.Compiler.Baker.Ingredients.PublishedFactRows.mapObligationInfo info |> ignore) |> ignore
        let withoutAccounts = {boundary with Calls=boundary.Calls |> Map.map (fun _ call -> {call with Arguments=call.Arguments |> List.map (fun operand -> {operand with OptionalEntry=None})})}
        Assert.False(Clef.Compiler.Baker.Recipes.ProofDispatchRecipes.optionalEntryPending graph withoutAccounts (id, info))
        let omitted = {selected with Emission={selected.Emission with Boundary=withoutAccounts}}
        match Clef.Compiler.Baker.Recipes.WitnessPublishedRowsRecipes.project graph scope omitted dispatch with
        | Result.Error failures -> Assert.Contains(failures, fun failure -> failure.Reason.Contains("Pending claim lacks its exact current optional-entry conversion account"))
        | Ok _ -> failwith "Optional Pending survived publication account omission"

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Optional receiving Pending dispatch rejects wrong family and withdrawn support``(withdrawSupport) =
        let result = ClosedCallbackCases.optionalCheck false false id
        DimensionalCases.noErrors result
        let graph = result.Graph
        let id, info =
            graph.Nodes |> Map.toList |> List.choose (fun (id, node) ->
                match node.Kind with
                | SemanticKind.Obligation info when info.Kind.StartsWith("foreign-optional-entry-conversion-") -> Some(id, info)
                | _ -> None) |> Assert.Single
        let changed =
            if withdrawSupport then
                {graph with Edges=graph.Edges |> List.filter (fun edge -> not (edge.Target=id && edge.Role=EdgeRole.Constrains))}
            else
                {graph with Nodes=graph.Nodes.Add(id, {graph.Nodes[id] with Kind=SemanticKind.Obligation {info with Kind="foreign-unrelated-pending"}})}
        match Clef.Compiler.Baker.Recipes.ProofDispatchRecipes.materialize changed with
        | Result.Ok {Query=Result.Error unavailable} -> Assert.Contains(unavailable, fun (claim, reasons) -> claim=id && not reasons.IsEmpty)
        | other -> failwithf "Unadmitted Pending acquired a ready query: %A" other

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Optional receiving shared claim matcher refuses changed canonical evidence``(present) =
        let result = ClosedCallbackCases.optionalCheck present false id
        DimensionalCases.noErrors result
        let graph = result.Graph
        let id, info =
            graph.Nodes |> Map.toList |> List.choose (fun (id, node) ->
                match node.Kind with
                | SemanticKind.Obligation info when info.Kind.StartsWith("foreign-optional-entry-conversion-") -> Some(id, info)
                | _ -> None) |> Assert.Single
        let calls = Clef.Compiler.Baker.Recipes.ProofDispatchRecipes.boundaryCalls graph
        Assert.True((Clef.Compiler.Baker.Recipes.BoundaryRecipes.optionalEntryClaimRows graph calls (id, info)) |> Result.isOk)
        let call = calls |> List.find (fun call -> call.Arguments |> List.exists (fun operand -> operand.OptionalEntry |> Option.exists (fun entry -> entry.Obligation=id)))
        let operand = call.Arguments |> List.find (fun operand -> operand.OptionalEntry.IsSome)
        let facts = graph.Codata.Value
        let account = facts.CallableAggregateDependencies[operand.Actual]
        let cases =
            [ "stale-source", "Callable aggregate source support changed after its dependency account was authored (CCS8414)."
              "stale-participant", "Callable aggregate source support changed after its dependency account was authored (CCS8414)."
              "source-support", "An optional-entry source account omits its semantic source incidences from the call support."
              "slot-role", "An optional-entry source account lacks its exact aggregate-slot participant role."
              "ordinal", "The optional-entry Pending claim has a different original argument ordinal."
              "identity", "The optional-entry Pending claim lost its source-owned claim identity."
              "reason", "The optional-entry Pending claim has different conversion reasons."
              "append-reason", "The optional-entry Pending claim has different conversion reasons."
              "unowned", "The optional-entry Pending claim lacks its exact owned ledger node."
              "remove-constrains", "The optional-entry Pending claim lost its exact ordered Constrains incidence."
              "duplicate-constrains", "The optional-entry Pending claim lost its exact ordered Constrains incidence."
              "added-constrains-source", "The optional-entry Pending claim lost its exact ordered Constrains incidence."
              "reordered-constrains-source", "The optional-entry Pending claim lost its exact ordered Constrains incidence."
              "remove-residence", "The optional-entry Pending claim lost its exact EnrichedWith residence."
              "duplicate-residence", "The optional-entry Pending claim lost its exact EnrichedWith residence." ]
        for change, reason in cases do
            let changed =
                match change with
                | "stale-source" | "stale-participant" | "slot-role" ->
                    let changedAccount =
                        match change with
                        | "stale-source" ->
                            let source = List.head account.Sources
                            {account with Sources={source with Anchors="changed-source-anchor"::source.Anchors}::List.tail account.Sources}
                        | "stale-participant" -> {account with Participants=List.head account.Participants::account.Participants}
                        | _ -> {account with Participants=account.Participants |> List.filter (fun participant -> participant.Role<>ParticipantRole.AggregateSlot)}
                    {graph with Codata=lazy {facts with CallableAggregateDependencies=facts.CallableAggregateDependencies.Add(operand.Actual, changedAccount)}}
                | "source-support" ->
                    let source = List.head account.Sources
                    let edges =
                        graph.Edges |> List.map (fun edge ->
                            match edge.Role with
                            | EdgeRole.BoundaryCall held when held.Site=call.Site -> {edge with Role=EdgeRole.BoundaryCall {held with Participants=held.Participants.Remove source.Node}}
                            | _ -> edge)
                    {graph with Edges=edges}
                | "identity" | "reason" | "append-reason" | "ordinal" | "unowned" ->
                    let claim =
                        match change with
                        | "identity" -> {info with Id=info.Id+"-changed"}
                        | "ordinal" -> {info with Kind="foreign-optional-entry-conversion-1"}
                        | "reason" -> {info with Body=ObligationBody.Pending ["Changed conversion premise."]}
                        | "append-reason" ->
                            let reasons = match info.Body with ObligationBody.Pending reasons -> reasons | _ -> []
                            {info with Body=ObligationBody.Pending (reasons @ ["Added conversion premise."])}
                        | _ -> info
                    let node = graph.Nodes[id]
                    let metadata = if change="unowned" then node.Metadata.Remove "Baker.BoundaryOwned" else node.Metadata
                    {graph with Nodes=graph.Nodes.Add(id, {node with Kind=SemanticKind.Obligation claim; Metadata=metadata})}
                | _ ->
                    let role = if change.Contains("constrains") then EdgeRole.Constrains else EdgeRole.EnrichedWith
                    let edge = graph.Edges |> List.filter (fun edge -> edge.Target=id && edge.Role=role) |> Assert.Single
                    if change.StartsWith("remove") then {graph with Edges=graph.Edges |> List.filter (fun edge -> not (edge.Target=id && edge.Role=role))}
                    elif change.StartsWith("duplicate") then {graph with Edges=graph.Edges @ [edge]}
                    else
                        let sources = if change.StartsWith("added") then edge.Sources @ [operand.Actual] else List.rev edge.Sources
                        Assert.NotEqual<NodeId list>(edge.Sources, sources)
                        {graph with Edges=graph.Edges |> List.map (fun held -> if held.Target=id && held.Role=role then {held with Sources=sources} else held)}
            let current = match changed.Nodes[id].Kind with SemanticKind.Obligation claim -> claim | other -> failwithf "%A" other
            let changedCalls = Clef.Compiler.Baker.Recipes.ProofDispatchRecipes.boundaryCalls changed
            match Clef.Compiler.Baker.Recipes.BoundaryRecipes.optionalEntryClaimRows changed changedCalls (id, current) with
            | Result.Error actual -> Assert.Equal(reason, actual)
            | Ok _ -> failwithf "Changed Pending evidence survived %s" change
            match Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission.project changed with
            | Result.Error failures ->
                let failure = failures |> Assert.Single
                Assert.Equal(Some id, failure.Occurrence)
                Assert.Equal("BoundaryEmission: The optional native callback lost its exact current per-use Pending conversion claim. " + reason, failure.Reason)
            | Ok _ -> failwithf "Changed Pending evidence reached publication after %s" change
            match Clef.Compiler.Baker.Recipes.ProofDispatchRecipes.materialize changed with
            | Result.Ok {Query=Result.Error unavailable} -> Assert.Contains(unavailable, fun (claim, reasons) -> claim=id && not reasons.IsEmpty)
            | other -> failwithf "Changed Pending evidence acquired a ready query after %s: %A" change other

    [<Fact>]
    member _.``Optional receiving source support keeps actual nodes separately from typed aggregate slots``() =
        let result = ClosedCallbackCases.optionalCheck false false id
        DimensionalCases.noErrors result
        let graph = result.Graph
        let selection = (read graph).OptionalReceiving |> Assert.Single
        let boundary =
            match Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission.project graph with
            | Ok boundary -> boundary
            | Result.Error failures -> failwithf "Optional boundary refused: %A" failures
        let call = boundary.Calls[selection.Call]
        let accounts = graph.Codata.Value.CallableAggregateDependencies
        let account = accounts[selection.Operand]
        match Clef.Compiler.Baker.Ingredients.Boundaries.optionalEntrySourceSupport accounts call 0 with
        | Result.Error reason -> failwith reason
        | Ok support ->
            let obligation = call.Arguments |> List.choose _.OptionalEntry |> List.exactlyOne |> _.Obligation
            let edge = graph.Edges |> List.filter (fun edge -> edge.Role=EdgeRole.Constrains && edge.Target=obligation) |> Assert.Single
            Assert.True(Set.isSubset support (Set.ofList edge.Sources))
            Assert.NotEmpty account.Slots
            for slot in account.Slots do
                Assert.Contains(account.Participants, fun participant -> participant.Node=slot.Identity && participant.Role=ParticipantRole.AggregateSlot)
                Assert.DoesNotContain(slot.Identity, call.Participants)
                Assert.DoesNotContain(slot.Identity, support)
                Assert.False(graph.Nodes.ContainsKey slot.Identity)
            for source in account.Sources do Assert.Contains(source.Node, support)
            Assert.Contains(selection.Construction, support)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Optional receiving source support refuses absent or changed aggregate slot roles``(changeRole) =
        let result = ClosedCallbackCases.optionalCheck false false id
        DimensionalCases.noErrors result
        let graph = result.Graph
        let selection = (read graph).OptionalReceiving |> Assert.Single
        let boundary =
            match Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission.project graph with
            | Ok boundary -> boundary
            | Result.Error failures -> failwithf "Optional boundary refused: %A" failures
        let call = boundary.Calls[selection.Call]
        let accounts = graph.Codata.Value.CallableAggregateDependencies
        let account = accounts[selection.Operand]
        let slots = account.Slots |> List.map _.Identity |> Set.ofList
        let participants = account.Participants |> List.choose (fun participant ->
            if participant.Role = ParticipantRole.AggregateSlot && slots.Contains participant.Node then
                if changeRole then Some {participant with Role=ParticipantRole.AggregateSource} else None
            else Some participant)
        let changed = accounts.Add(selection.Operand, {account with Participants=participants})
        match Clef.Compiler.Baker.Ingredients.Boundaries.optionalEntrySourceSupport changed call 0 with
        | Result.Error reason -> Assert.Equal("An optional-entry source account lacks its exact aggregate-slot participant role.", reason)
        | Ok _ -> failwith "An untyped aggregate relation identity entered the semantic source constraint domain"

    [<Fact>]
    member _.``A binding adapter hides native arguments from a closed application handler``() =
        let body = """
let handler (value: int) : unit = ()
[<EntryPoint>]
let main _ = let entry = listener handler in 0
"""
        let result = ClosedCallbackCases.check (ClosedCallbackCases.declarations + body)
        DimensionalCases.noErrors result
        let entry = ClosedCallbackCases.entries result.Graph |> Assert.Single
        match result.Graph.Nodes[entry.Lambda].Kind with
        | SemanticKind.Lambda (parameters, _, captures, _, _) ->
            Assert.Equal(2, parameters.Length)
            Assert.Empty captures
        | kind -> failwithf "Expected native module entry, got %A" kind
        Assert.Contains("handler", ClosedCallbackCases.handlerReferences result.Graph)
        Assert.True(entry.ReturnsVoid)
        Assert.Contains(result.Graph.Codata.Value.FunctionPointers |> Map.values, function
            | FunctionPointerPlan.Address (symbol, target) -> target = entry.Lambda && symbol.StartsWith("__clef_callback_")
            | _ -> false)

    [<Fact>]
    member _.``Different closed handlers retain distinct native entries``() =
        let body = """
let handlerOne (value: int) : unit = ()
let handlerTwo (value: int) : unit = ()
[<EntryPoint>]
let main _ =
    let first = listener handlerOne
    let second = listener handlerTwo
    0
"""
        let result = ClosedCallbackCases.check (ClosedCallbackCases.declarations + body)
        DimensionalCases.noErrors result
        let entries = ClosedCallbackCases.entries result.Graph
        Assert.Equal(2, entries.Length)
        Assert.Equal(2, entries |> List.map (fun entry -> entry.Lambda) |> List.distinct |> List.length)
        Assert.Contains("handlerOne", ClosedCallbackCases.handlerReferences result.Graph)
        Assert.Contains("handlerTwo", ClosedCallbackCases.handlerReferences result.Graph)

    [<Theory>]
    [<InlineData("let captured (value: int) = if value = limit then () else ()\n    let entry = listener captured\n    0")>]
    [<InlineData("let entry = listener (fun value -> if value = limit then () else ())\n    0")>]
    member _.``A captured handler is rejected before any C address is created``(body: string) =
        let result = ClosedCallbackCases.check (ClosedCallbackCases.declarations + "\n[<EntryPoint>]\nlet main _ =\n    let limit = 7\n    " + body + "\n")
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8096")
        Assert.Empty(ClosedCallbackCases.entries result.Graph)

    [<Fact>]
    member _.``The adapter requires a declared native ABI``() =
        let source = ClosedCallbackCases.declarations.Split('\n') |> Array.filter (fun line -> not (line.StartsWith("let entryDescriptor:"))) |> String.concat "\n"
        let result = ClosedCallbackCases.check (source + "\nlet handler (value: int) = ()\n[<EntryPoint>]\nlet main _ = let entry = listener handler in 0\n")
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8096" && diagnostic.Message.Contains("CallbackDescriptor"))

    [<Fact>]
    member _.``Native scalar mismatches remain errors after specialization``() =
        let source = ClosedCallbackCases.declarations.Replace("Type = Integer (Signed, 32)", "Type = Pointer 64")
        let result = ClosedCallbackCases.check (source + "\nlet handler (value: int) = ()\n[<EntryPoint>]\nlet main _ = let entry = listener handler in 0\n")
        Assert.Contains((read result.Graph).Findings, fun finding -> finding.Defect = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.DeclarationDefect.Invalid)

    [<Theory>]
    [<InlineData("let private adapter (handler: int -> unit) (value: int) (_data: CHandle<unit>) : unit = handler value", "let mutable adapter = fun (handler: int -> unit) (value: int) (_data: CHandle<unit>) -> handler value")>]
    [<InlineData("let private makeEntry (handler: int -> unit) : NativeEntry = NativeDefault.zeroed ()", "let mutable makeEntry = fun (handler: int -> unit) -> (NativeDefault.zeroed () : NativeEntry)")>]
    member _.``Mutable template declarations cannot be statically substituted``(original: string, replacement: string) =
        let source = ClosedCallbackCases.declarations.Replace(original, replacement)
        let result = ClosedCallbackCases.check (source + "\nlet handler (value: int) = ()\n[<EntryPoint>]\nlet main _ = let entry = listener handler in 0\n")
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8096")
        Assert.Empty(ClosedCallbackCases.entries result.Graph)

    [<Fact>]
    member _.``A nested closure cannot retain the removed handler formal``() =
        let source = ClosedCallbackCases.declarations.Replace("= handler value", "= let later () = handler value in later ()")
        let result = ClosedCallbackCases.check (source + "\nlet handler (value: int) = ()\n[<EntryPoint>]\nlet main _ = let entry = listener handler in 0\n")
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8096" && diagnostic.Message.Contains("nested closure"))

    [<Fact>]
    member _.``A local descriptor cannot declare the native ABI``() =
        let source = ClosedCallbackCases.declarations.Replace("let entryDescriptor:", "let localDeclaration () =\n    let entryDescriptor:").Replace("let private adapter", "    ()\nlet private adapter")
        let result = ClosedCallbackCases.check (source + "\nlet handler (value: int) = ()\n[<EntryPoint>]\nlet main _ = let entry = listener handler in 0\n")
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8096" && diagnostic.Message.Contains("CallbackDescriptor"))

    [<Fact>]
    member _.``A saturated inline call checks even an unused argument's declared type``() =
        let result =
            match parseAndCheck "module InlineCheck\nlet inline keep (x: int) (y: int) = x\n[<EntryPoint>]\nlet main _ = keep 1 \"bad\"" "inline-check.clef" with
            | Success result | CheckFailure result -> result
            | ParseFailure errors -> failwithf "%A" errors
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Severity = NativeDiagnosticSeverity.Error)

    [<Fact>]
    member _.``Inline names resolve at the definition even when the caller shadows them``() =
        let library = "module Library\nlet helper (x: int) = x + 1\nlet inline apply (first: int) (second: int) = helper (first + second)"
        let application = "module Application\nlet helper (x: string) = x\n[<EntryPoint>]\nlet main _ = Library.apply 3 4"
        let inputs =
            [library, "inline-library.clef"; application, "inline-caller.clef"]
            |> List.map (fun (text, path) ->
                match parseStringWithDefaults text path with
                | ParseSuccess input -> input
                | ParseError errors -> failwithf "%A" errors)
        let result = checkParsedInputs inputs
        DimensionalCases.noErrors result
        Assert.Contains(result.Graph.Nodes.Values, fun node ->
            node.IsReachable && node.Range.File = "inline-library.clef"
            && match node.Kind with SemanticKind.Binding ("helper", _, _, _) -> true | _ -> false)

    [<Fact>]
    member _.``A declared factory cannot escape through an ordinary function alias``() =
        let source = ClosedCallbackCases.declarations
        let result = ClosedCallbackCases.check (source + "\nlet handler (value: int) = ()\n[<EntryPoint>]\nlet main _ =\n    let factory = ClosedCallbacks.makeEntry\n    let entry = factory handler\n    0\n")
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8096" && diagnostic.Message.Contains("escape"))

    [<Fact>]
    member _.``Inline annotation parameters are fresh at each use``() =
        let source = "module GenericInline\nlet inline keep<'T> (x: 'T) (_y: 'T) =\n    let result: 'T = x\n    result\n[<EntryPoint>]\nlet main _ =\n    let count = keep 1 2\n    let text = keep \"a\" \"b\"\n    count"
        let result =
            match parseAndCheck source "generic-inline.clef" with
            | Success result | CheckFailure result -> result
            | ParseFailure errors -> failwithf "%A" errors
        DimensionalCases.noErrors result

    [<Fact>]
    member _.``Inline measure annotations are fresh at each use``() =
        let source = "module MeasuredInline\n[<Measure>] type m\n[<Measure>] type s\nlet inline keep (x: int<'u>) (_y: int<'u>) =\n    let result: int<'u> = x\n    result\n[<EntryPoint>]\nlet main _ =\n    let length = keep 1<m> 2<m>\n    let time = keep 1<s> 2<s>\n    0"
        let result =
            match parseAndCheck source "measured-inline.clef" with
            | Success result | CheckFailure result -> result
            | ParseFailure errors -> failwithf "%A" errors
        DimensionalCases.noErrors result

    [<Fact>]
    member _.``Specialization cannot discard effects in a factory body``() =
        let source = ClosedCallbackCases.declarations.Replace("NativeEntry = NativeDefault.zeroed ()", "NativeEntry = handler 1; NativeDefault.zeroed ()")
        let result = ClosedCallbackCases.check (source + "\nlet handler (value: int) = ()\n[<EntryPoint>]\nlet main _ = let entry = listener handler in 0\n")
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8096" && diagnostic.Message.Contains("exactly NativeDefault.zeroed"))

    [<Fact>]
    member _.``Receiving callback unused native formal preserves ABI64``() =
        let graph = ClosedCallbackCases.receivingGraph ()
        let entry = (read graph).Receiving |> Assert.Single
        let formal, declared = entry.Signature.Parameters |> Assert.Single
        Assert.Equal(64, declared.Value.Bits)
        Assert.Equal(Some(ValueRange.twosComplement 64), graph.Nodes[formal].ValueRange)

        match graph.Nodes[entry.Lambda].Kind with
        | SemanticKind.Lambda(parameters, _, captures, _, _) ->
            Assert.Equal(formal, parameters |> List.exactlyOne |> fun (_, _, id) -> id)
            Assert.Empty captures
        | kind -> failwithf "Expected full callback lambda: %A" kind

        Assert.DoesNotContain(
            graph.Nodes.Values,
            fun node ->
                match node.Kind with
                | SemanticKind.VarRef(_, Some target) -> target = formal
                | _ -> false
        )

        match Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project graph with
        | Ok numeric -> Assert.Equal(ValueRange.twosComplement 64, numeric.Values[formal].Range)
        | Result.Error failures -> failwithf "Current incoming numeric evidence refused: %A" failures

    [<Fact>]
    member _.``Receiving callback changed hypothesis invalidates numeric premises``() =
        let graph = ClosedCallbackCases.receivingGraph ()

        let declarations =
            Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.readDescriptors graph

        let invocation = declarations.CallbackInvocations |> Assert.Single

        let _, fields =
            Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.recordOf graph invocation.Node
            |> Option.get

        let _, hypothesis =
            Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.field "Hypothesis" fields
            |> Option.bind (Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.recordOf graph)
            |> Option.get

        let version, _ =
            Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.field "Version" hypothesis
            |> Option.bind (Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.valuePath graph)
            |> Option.get

        let changed =
            { graph with
                Nodes =
                    graph.Nodes.Add(
                        version.Id,
                        { version with
                            Kind = SemanticKind.Literal(NativeLiteral.String "v2")
                        }
                    )
            }

        match Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project changed with
        | Result.Error failures ->
            Assert.Contains(
                failures,
                fun failure ->
                    failure.Reason =
                        "NumericPublication: Invocation-context range premises changed or the producer receipt is absent; source range settlement is required."
            )
        | Ok _ -> failwith "Changed receiving hypothesis retained old numeric evidence"


    [<Fact>]
    member _.``Receiving record projection retains original native callback account``() =
        let graph = ClosedCallbackCases.receivingWrapperGraph ()
        let association = (read graph).Receiving |> Assert.Single

        let boundary =
            match Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission.project graph with
            | Ok boundary -> boundary
            | Result.Error errors -> failwithf "Projected callback source publication refused: %A" errors

        let closed = boundary.ClosedEntries.Values |> Assert.Single
        Assert.Equal(association.Address, closed.Formation)
        Assert.Contains(association.Operand, closed.Transport)

        let projection =
            graph.Codata.Value.CallableAggregateValues[association.Operand] |> Assert.Single

        Assert.Equal(CallableAggregateOperation.Project, projection.Operation)
        Assert.Equal(closed.Formation, projection.Alternatives.Head.Formation)
        let formal = closed.Formals |> Assert.Single
        Assert.Equal(Some(ValueRange.twosComplement 64), graph.Nodes[formal].ValueRange)

        match graph.Nodes[association.Operand].Kind with
        | SemanticKind.FieldGet(_, "Handler") -> ()
        | kind -> failwithf "The generic declared record field was not retained: %A" kind

    [<Fact>]
    member _.``Receiving record projection refuses coherently withdrawn supplier``() =
        let graph = ClosedCallbackCases.receivingWrapperGraph ()
        let association = (read graph).Receiving |> Assert.Single
        let facts = graph.Codata.Value
        let projection = facts.CallableAggregateValues[association.Operand] |> Assert.Single
        let construction = projection.FormationInputs.Head

        let withdrawn =
            { graph with
                Codata =
                    lazy
                        { facts with
                            CallableAggregateValues = facts.CallableAggregateValues.Remove construction
                        }
            }
        // Renew only the held aggregate account. The source Project and native
        // signature remain intact, so an old-account mismatch cannot kill this test.
        let account =
            match Clef.Compiler.Baker.Ingredients.CallableAggregateAccounts.author withdrawn association.Operand with
            | Ok account -> account
            | Result.Error reason -> failwith reason

        let renewed =
            { withdrawn.Codata.Value with
                CallableAggregateDependencies = facts.CallableAggregateDependencies.Add(association.Operand, account)
            }

        let changed = { withdrawn with Codata = lazy renewed }

        match Clef.Compiler.Baker.Ingredients.CallableAggregateAccounts.current changed association.Operand with
        | Ok _ -> ()
        | Result.Error reason -> failwithf "Coherent account renewal failed: %s" reason

        match Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission.project changed with
        | Result.Error failures ->
            Assert.Contains(
                failures,
                fun failure -> failure.Reason = "BoundaryEmission: The receiving projection has no exact admitted supplying construction."
            )
        | Ok _ -> failwith "The receiving projection survived withdrawal of its supplying construction"


    [<Fact>]
    member _.``Receiving record account retains ordinary body but excludes foreign placeholder``() =
        let graph = ClosedCallbackCases.receivingWrapperGraph ()
        let association = (read graph).Receiving |> Assert.Single
        let account = graph.Codata.Value.CallableAggregateDependencies[association.Operand]

        let _, wrapper =
            graph.Nodes
            |> Map.toSeq
            |> Seq.find (fun (_, node) ->
                match node.Kind with
                | SemanticKind.Binding("receiveRecord", _, _, _) -> true
                | _ -> false)

        let implementation = graph.Nodes[wrapper.Children |> List.exactlyOne]

        let body =
            match implementation.Kind with
            | SemanticKind.Lambda(_, body, _, _, _) -> body
            | kind -> failwithf "Expected exact ordinary wrapper declaration: %A" kind

        Assert.Contains(account.Sources, fun source -> source.Node = body)

        let foreignBodies =
            graph.Edges
            |> List.choose (fun edge ->
                match edge.Role with
                | EdgeRole.BoundaryDeclaration declaration -> Some declaration.Body
                | _ -> None)

        Assert.NotEmpty foreignBodies

        for placeholder in foreignBodies do
            Assert.DoesNotContain(account.Sources, fun source -> source.Node = placeholder)

        let changed =
            { graph with
                Nodes = graph.Nodes.Remove body
            }

        match Clef.Compiler.Baker.Ingredients.CallableAggregateAccounts.current changed association.Operand with
        | Result.Error reason ->
            Assert.Equal("Callable aggregate source support changed after its dependency account was authored (CCS8414).", reason)
        | Ok _ -> failwith "Withdrawing an ordinary wrapper body retained its old dependency account"


    [<Fact>]
    member _.``Receiving record public replay refuses withdrawn projection account``() =
        let graph = ClosedCallbackCases.receivingWrapperGraph ()

        let revision =
            match Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph with
            | Ok revision -> revision
            | Result.Error failures -> failwithf "Source callback revision refused: %A" failures

        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let call = revision.Emission.Boundary.Calls.Values |> Assert.Single

        let operand =
            call.Arguments
            |> List.filter (fun operand ->
                match operand.Abi with
                | Fidelity.PSG.BoundaryScalar.Entry _ -> true
                | _ -> false)
            |> Assert.Single

        let callable = revision.Emission.Callable

        let withdrawn =
            { callable with
                AggregateValues = callable.AggregateValues.Remove operand.Actual
                AggregateDependencies = callable.AggregateDependencies.Remove operand.Actual
            }

        let changed =
            { revision with
                Codata =
                    { revision.Codata with
                        CallableAggregateValues = withdrawn.AggregateValues
                        CallableAggregateDependencies = withdrawn.AggregateDependencies
                    }
                Emission =
                    { revision.Emission with
                        Callable = withdrawn
                    }
            }

        Assert.Contains(
            Fidelity.PSG.Integrity.check changed,
            fun failure ->
                failure.Part = "Emission.Boundary.Calls.CallbackProjection"
                && failure.Reason = "The projected callback argument lacks its exact original closed-entry aggregate account."
        )

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Receiving integer pair preserves every ordered native formal and codec``(useSecond: bool) =
        let graph = ClosedCallbackCases.receivingPairGraph useSecond
        let receiving = (read graph).Receiving |> Assert.Single
        let formals = receiving.Signature.Parameters |> List.map fst
        Assert.Equal(2, formals.Length)
        for formal, declared in receiving.Signature.Parameters do
            Assert.Equal(64, declared.Value.Bits)
            Assert.Equal(Some(ValueRange.twosComplement 64), graph.Nodes[formal].ValueRange)
        match graph.Nodes[receiving.Lambda].Kind with
        | SemanticKind.Lambda(parameters, _, captures, _, _) ->
            Assert.True((parameters |> List.map (fun (_, _, id) -> id)) = formals)
            Assert.Empty captures
        | kind -> failwithf "Expected complete two-formal native lambda: %A" kind
        let uses formal =
            graph.Nodes.Values |> Seq.exists (fun node ->
                match node.Kind with SemanticKind.VarRef(_, Some target) -> target = formal | _ -> false)
        Assert.False(uses formals.Head)
        Assert.Equal(useSecond, uses formals[1])
        match Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project graph with
        | Ok numeric ->
            for formal in formals do Assert.Equal(ValueRange.twosComplement 64, numeric.Values[formal].Range)
        | Result.Error failures -> failwithf "Complete incoming pair domains refused: %A" failures
        let revision =
            Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph
            |> Result.defaultWith (fun errors -> failwithf "Pair source publication refused: %A" errors)
        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let entry = revision.Emission.Boundary.ClosedEntries.Values |> Assert.Single
        let invocation = revision.Emission.Boundary.CallbackInvocations[entry.Invocation]
        Assert.Equal(2, entry.Formals.Length)
        Assert.Equal(2, entry.ParameterAdaptations.Length)
        Assert.True(invocation.Signature.Parameters = [Fidelity.PSG.BoundaryScalar.Integer(64, true); Fidelity.PSG.BoundaryScalar.Integer(64, true)])
        let limits: Fidelity.PSG.Binary.Limits =
            { MaxBytes = 8 * 1024 * 1024; MaxCollectionLength = 100000; MaxDepth = 128
              MaxStringBytes = 1024 * 1024; MaxBigIntegerBytes = 4096; MaxValues = 2000000 }
        let bytes =
            Fidelity.PSG.Binary.encode limits revision
            |> Result.defaultWith (fun error -> failwithf "Pair codec refused: %A" error)
        let copy =
            Fidelity.PSG.Binary.decode limits bytes
            |> Result.defaultWith (fun error -> failwithf "Pair codec refused: %A" error)
        Assert.True(copy.Emission.Boundary.CallbackInvocations = revision.Emission.Boundary.CallbackInvocations)
        Assert.True(copy.Emission.Boundary.ClosedEntries = revision.Emission.Boundary.ClosedEntries)

    [<Theory>]
    [<InlineData("missing-formal")>]
    [<InlineData("arity")>]
    [<InlineData("order")>]
    [<InlineData("boolean")>]
    [<InlineData("empty")>]
    member _.``Receiving integer pair public account refuses exact withdrawal``(shape: string) =
        let graph = ClosedCallbackCases.receivingPairGraph false
        let revision =
            Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph
            |> Result.defaultWith (fun errors -> failwithf "Pair source publication refused: %A" errors)
        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let boundary = revision.Emission.Boundary
        let entry = boundary.ClosedEntries.Values |> Assert.Single
        let invocation = boundary.CallbackInvocations[entry.Invocation]
        let changed, part =
            match shape with
            | "missing-formal" ->
                { boundary with ClosedEntries = boundary.ClosedEntries.Add(entry.Formation, {entry with Formals = entry.Formals.Tail; ParameterAdaptations = entry.ParameterAdaptations.Tail}) }, "Emission.Boundary.ClosedEntries.Declaration"
            | "order" ->
                { boundary with ClosedEntries = boundary.ClosedEntries.Add(entry.Formation, {entry with Formals = List.rev entry.Formals; ParameterAdaptations = List.rev entry.ParameterAdaptations}) }, "Emission.Boundary.ClosedEntries.Declaration"
            | "arity" ->
                let invocation = { invocation with Signature = { invocation.Signature with Parameters = invocation.Signature.Parameters.Tail } }
                { boundary with CallbackInvocations = boundary.CallbackInvocations.Add(invocation.Identity, invocation) }, "Emission.Boundary.CallbackInvocations.Signature"
            | "boolean" ->
                let parameters = Array.copy invocation.Contract.Signature.Parameters
                parameters[0] <- { parameters[0] with Type = BAREWire.Descriptors.TypeRef.Bool }
                let invocation =
                    { invocation with
                        Signature = { invocation.Signature with Parameters = Fidelity.PSG.BoundaryScalar.Boolean :: invocation.Signature.Parameters.Tail }
                        Contract = { invocation.Contract with Signature = { invocation.Contract.Signature with Parameters = parameters } } }
                { boundary with CallbackInvocations = boundary.CallbackInvocations.Add(invocation.Identity, invocation) }, "Emission.Boundary.CallbackInvocations.Signature"
            | "empty" ->
                let invocation =
                    { invocation with
                        Signature = { invocation.Signature with Parameters = [] }
                        Contract = { invocation.Contract with Signature = { invocation.Contract.Signature with Parameters = [||] } } }
                { boundary with CallbackInvocations = boundary.CallbackInvocations.Add(invocation.Identity, invocation) }, "Emission.Boundary.CallbackInvocations.Signature"
            | _ -> failwithf "Unknown withdrawal %s" shape
        let changed = { revision with Emission = { revision.Emission with Boundary = changed } }
        let reason =
            if part = "Emission.Boundary.ClosedEntries.Declaration" then
                "The closed entry differs from its original capture-free implementation, body or complete ordered native formals."
            else
                "The callback signature differs from its complete nonempty integer-formal CDecl receiving quotation and exact integer or void result."
        Assert.Contains(Fidelity.PSG.Integrity.check changed, fun error -> error.Part = part && error.Reason = reason)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Receiving unit result preserves full integer domains and an empty native result through codec``(mixed: bool) =
        let graph = ClosedCallbackCases.receivingUnitGraph mixed
        let receiving = (read graph).Receiving |> Assert.Single
        Assert.Equal(2, receiving.Signature.Parameters.Length)
        Assert.True receiving.Signature.Return.IsNone
        let body = receiving.Signature.Body.Value
        Assert.Equal(Some NTUKind.NTUunit, Types.tryGetNTUKind graph.Nodes[body].Type)
        Assert.False(graph.Codata.Value.ReturnMeets.ContainsKey receiving.Lambda)

        let expected =
            if mixed then
                [ ValueRange.twosComplement 32; ValueRange.unsignedOf 64 ]
            else
                [ ValueRange.twosComplement 64; ValueRange.twosComplement 64 ]

        let numeric =
            Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project graph
            |> Result.defaultWith (fun errors -> failwithf "Unit incoming domains refused: %A" errors)

        for (formal, declared), domain in List.zip receiving.Signature.Parameters expected do
            Assert.Equal(domain, declared.Value.Range)
            Assert.Equal(domain, numeric.Values[formal].Range)

        Assert.False(numeric.Values.ContainsKey body)

        let revision =
            Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph
            |> Result.defaultWith (fun errors -> failwithf "Unit source publication refused: %A" errors)

        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let entry = revision.Emission.Boundary.ClosedEntries.Values |> Assert.Single
        let invocation = revision.Emission.Boundary.CallbackInvocations[entry.Invocation]
        Assert.Equal(BAREWire.Descriptors.TypeRef.Void, invocation.Contract.Signature.ReturnType)
        Assert.True(invocation.Signature.Result.IsNone && entry.ResultAdaptation.IsNone)
        Assert.True(Fidelity.PSG.TypeIdentity.isUnit revision.Nodes[entry.Body].Type)
        Assert.Contains(entry.Body, revision.Emission.Callable.UnitNodes)
        Assert.Equal(2, entry.Formals.Length)
        Assert.False(revision.Emission.Numeric.Values.ContainsKey entry.Body)

        let limits: Fidelity.PSG.Binary.Limits =
            {
                MaxBytes = 8 * 1024 * 1024
                MaxCollectionLength = 100000
                MaxDepth = 128
                MaxStringBytes = 1024 * 1024
                MaxBigIntegerBytes = 4096
                MaxValues = 2000000
            }

        let bytes =
            Fidelity.PSG.Binary.encode limits revision
            |> Result.defaultWith (fun error -> failwithf "%A" error)

        let copy =
            Fidelity.PSG.Binary.decode limits bytes
            |> Result.defaultWith (fun error -> failwithf "%A" error)

        Assert.True(revision.Emission.Boundary = copy.Emission.Boundary)

    [<Theory>]
    [<InlineData("missing-void")>]
    [<InlineData("body")>]
    [<InlineData("unit-fact")>]
    [<InlineData("result")>]
    member _.``Receiving unit public account refuses missing void or actual unit evidence``(shape: string) =
        let revision =
            ClosedCallbackCases.receivingUnitGraph false
            |> Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish
            |> Result.defaultWith (fun errors -> failwithf "Unit source publication refused: %A" errors)

        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let boundary = revision.Emission.Boundary
        let entry = boundary.ClosedEntries.Values |> Assert.Single
        let invocation = boundary.CallbackInvocations[entry.Invocation]

        let withInvocation (invocation: Fidelity.PSG.BoundaryCallbackInvocation) =
            { revision with
                Emission =
                    { revision.Emission with
                        Boundary =
                            { boundary with
                                CallbackInvocations = boundary.CallbackInvocations.Add(invocation.Identity, invocation)
                            }
                    }
            }

        let changed, part, reason =
            if shape = "missing-void" || shape = "result" then
                let invocation =
                    if shape = "missing-void" then
                        { invocation with
                            Contract =
                                { invocation.Contract with
                                    Signature =
                                        { invocation.Contract.Signature with
                                            ReturnType = BAREWire.Descriptors.TypeRef.Pointer 64
                                        }
                                }
                        }
                    else
                        { invocation with
                            Signature =
                                { invocation.Signature with
                                    Result = Some(Fidelity.PSG.BoundaryScalar.Integer(64, true))
                                }
                        }

                withInvocation invocation,
                "Emission.Boundary.CallbackInvocations.Signature",
                "The callback signature differs from its complete nonempty integer-formal CDecl receiving quotation and exact integer or void result."
            else
                let changed =
                    if shape = "unit-fact" then
                        { revision with
                            Emission =
                                { revision.Emission with
                                    Callable =
                                        { revision.Emission.Callable with
                                            UnitNodes = revision.Emission.Callable.UnitNodes.Remove entry.Body
                                        }
                                }
                        }
                    else
                        let body = revision.Nodes[entry.Body]

                        let wrongType =
                            match body.Type with
                            | Fidelity.PSG.TypeIdentity.Application(constructor, arguments) ->
                                Fidelity.PSG.TypeIdentity.Application(
                                    { constructor with
                                        NativeKind = Some Fidelity.PSG.NTUKind.NTUbool
                                    },
                                    arguments
                                )
                            | _ -> failwith "Expected the actual source unit type."

                        { revision with
                            Nodes = revision.Nodes.Add(entry.Body, { body with Type = wrongType })
                        }

                changed,
                "Emission.Boundary.ClosedEntries.UnitResult",
                "A void native callback requires its actual unit source body and no numeric result or return adaptation."

        let failures = Fidelity.PSG.Integrity.check changed
        Assert.Contains(failures, fun error -> error.Part = part && error.Reason = reason)
        if shape = "missing-void" then Assert.Single failures |> ignore

    [<Fact>]
    member _.``Receiving integer pair refuses source callback with missing native formal``() =
        let result =
            ClosedCallbackCases.receivingCheckWith false
                (ClosedCallbackCases.pairSource "let callback (_first: int) = 7")
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8207" && diagnostic.Message.Contains("declares 2 parameters; the binding takes 1"))
        Assert.Empty(result.Graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryClosedEntry entry -> Some entry | _ -> None))

    [<Fact>]
    member _.``Mixed receiving callback blocks publish immediate meets without a duplicate return cast``() =
        let callback =
            """let callback (first: int) (second: int) =
    let marker = second
    if first < 0 then
        if second > 9223372036854775807 then 4294967295 else 0
    else 0"""

        let result =
            ClosedCallbackCases.receivingCheckWith false (fun source ->
                let paired = ClosedCallbackCases.pairSource callback source

                paired
                    .Replace("{ Name = \"arg0\"; Type = Integer (Signed, 64)", "{ Name = \"arg0\"; Type = Integer (Signed, 32)")
                    .Replace("{ Name = \"arg1\"; Type = Integer (Signed, 64)", "{ Name = \"arg1\"; Type = Integer (Unsigned, 64)")
                    .Replace("ReturnType = Integer (Signed, 64)", "ReturnType = Integer (Unsigned, 32)"))

        DimensionalCases.noErrors result
        let graph = result.Graph
        let receiving = (read graph).Receiving |> Assert.Single
        let body = receiving.Signature.Body.Value

        let child =
            match graph.Nodes[body].Kind with
            | SemanticKind.Sequential values -> List.last values
            | kind -> failwithf "Expected source block, got %A" kind

        let bodyMeet = graph.Codata.Value.Meets[body] |> Assert.Single
        Assert.Equal(body, bodyMeet.Consumer)
        Assert.Equal(child, bodyMeet.Operand)
        Assert.Equal(64, bodyMeet.From)
        Assert.Equal(32, bodyMeet.To)
        Assert.Equal(MeetKind.Truncate, bodyMeet.Adapt)
        Assert.False(graph.Codata.Value.ReturnMeets.ContainsKey receiving.Lambda)

        let numeric =
            Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project graph
            |> Result.defaultWith (sprintf "%A" >> failwith)

        Assert.Equal(ValueRange.Bounded(0I, 4294967295I), numeric.Values[body].Range)
        Assert.Equal(SettledSlot.Integer(32, Some "unsigned32"), numeric.Values[body].Slot)
        Assert.NotEmpty numeric.Values[body].Obligations

        for formal, declared in receiving.Signature.Parameters do
            Assert.Equal(Some declared.Value.Range, graph.Nodes[formal].ValueRange)

        let revision =
            Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph
            |> Result.defaultWith (sprintf "%A" >> failwith)

        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let native = revision.Emission.Boundary.ClosedEntries.Values |> Assert.Single
        Assert.True(native.ResultAdaptation.IsNone)

        Assert.Equal(
            [ 32; 64 ],
            revision.Emission.Boundary.CallbackInvocations[native.Invocation].Signature.Parameters
            |> List.map (function
                | Fidelity.PSG.BoundaryScalar.Integer(bits, _) -> bits
                | value -> failwithf "%A" value)
        )

        let publishedMeet = revision.Codata.Meets[Fidelity.PSG.NodeId(NodeId.value body)] |> Assert.Single
        Assert.Equal(Fidelity.PSG.NodeId(NodeId.value bodyMeet.Consumer), publishedMeet.Consumer)
        Assert.Equal(Fidelity.PSG.NodeId(NodeId.value bodyMeet.Operand), publishedMeet.Operand)
        Assert.Equal(bodyMeet.From, publishedMeet.From)
        Assert.Equal(bodyMeet.To, publishedMeet.To)
        let withdrawn = { graph with Platform = None }

        let derives =
            Clef.Compiler.PSGSaturation.SemanticGraph.Meets.derive None withdrawn withdrawn.Codata.Value.Curry

        Assert.False(derives.ContainsKey body)

        match Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project withdrawn with
        | Result.Error failures ->
            Assert.Contains(failures, fun failure -> failure.Reason = "NumericPublication: Invocation-context range premises changed or the producer receipt is absent; source range settlement is required.")
        | Ok _ -> failwith "Withdrawn selected platform retained current mixed carrier evidence"

    [<Fact>]
    member _.``Equal native block carrier does not fabricate a forwarding or return meet``() =
        let graph =
            ClosedCallbackCases.receivingCheckWith false (fun source ->
                source.Replace("let callback (_unused: int) = 7", "let callback (_unused: int) =\n    let value = _unused\n    value"))

        DimensionalCases.noErrors graph
        let receiving = (read graph.Graph).Receiving |> Assert.Single
        let body = receiving.Signature.Body.Value
        Assert.False(graph.Graph.Codata.Value.Meets.ContainsKey body)
        Assert.False(graph.Graph.Codata.Value.ReturnMeets.ContainsKey receiving.Lambda)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Sole source unit formal is retained while its native vector is empty``(used: bool) =
        let callback =
            if used then
                "let callback (value: unit) : unit =\n    let marker = 7\n    value"
            else
                "let callback (_unused: unit) : unit = ()"

        let result = ClosedCallbackCases.receivingZeroCheck callback
        DimensionalCases.noErrors result

        let revision =
            Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish result.Graph
            |> Result.defaultWith (fun errors -> failwithf "Sole unit publication refused: %A" errors)

        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let entry = revision.Emission.Boundary.ClosedEntries.Values |> Assert.Single
        let formal = entry.Formals |> Assert.Single
        let invocation = revision.Emission.Boundary.CallbackInvocations[entry.Invocation]
        let carrier = revision.Emission.Callable.Carriers[entry.Formation]

        let contract =
            carrier.Contract
            |> Result.defaultWith failwith
            |> fun identity -> revision.Emission.Callable.Contracts[identity]

        Assert.Empty invocation.Contract.Signature.Parameters
        Assert.Empty invocation.Signature.Parameters
        Assert.Equal(BAREWire.Descriptors.TypeRef.Void, invocation.Contract.Signature.ReturnType)
        Assert.True invocation.Signature.Result.IsNone
        Assert.True(Set.singleton formal = carrier.OmittedParameters)
        Assert.Equal<int list>([ 0 ], contract.OmittedParameters)
        Assert.Empty contract.ParameterRepresentations
        Assert.True(Fidelity.PSG.TypeIdentity.isUnit revision.Nodes[formal].Type)
        Assert.Contains(formal, revision.Emission.Callable.UnitNodes)
        Assert.Equal<Fidelity.PSG.Meet option list>([ None ], entry.ParameterAdaptations)
        Assert.True(entry.ResultAdaptation.IsNone)
        Assert.False(revision.Emission.Numeric.Values.ContainsKey formal)
        Assert.False(revision.Emission.Numeric.Values.ContainsKey entry.Body)

        let limits: Fidelity.PSG.Binary.Limits =
            {
                MaxBytes = 8 * 1024 * 1024
                MaxCollectionLength = 100000
                MaxDepth = 128
                MaxStringBytes = 1024 * 1024
                MaxBigIntegerBytes = 4096
                MaxValues = 2000000
            }

        let bytes =
            Fidelity.PSG.Binary.encode limits revision
            |> Result.defaultWith (fun error -> failwithf "%A" error)

        let copy =
            Fidelity.PSG.Binary.decode limits bytes
            |> Result.defaultWith (fun error -> failwithf "%A" error)

        Assert.Equal(revision.Emission.Boundary, copy.Emission.Boundary)
        Assert.True(carrier.OmittedParameters = copy.Emission.Callable.Carriers[entry.Formation].OmittedParameters)

    [<Theory>]
    [<InlineData("let callback (_unused: int) : unit = ()")>]
    [<InlineData("let callback (_first: unit) (_second: unit) : unit = ()")>]
    member _.``Empty native vector refuses a source formal vector without exact sole unit``(callback: string) =
        let signature =
            if callback.Contains("_first") then
                "unit -> unit -> unit"
            else
                "int -> unit"

        let result = ClosedCallbackCases.receivingZeroCheckWith signature callback

        Assert.Contains(
            result.Diagnostics,
            fun diagnostic ->
                diagnostic.Code = "CCS8413"
                && diagnostic.Message = "Callable receiving convention has not been settled by its source recipe."
        )

    [<Theory>]
    [<InlineData("type")>]
    [<InlineData("representation")>]
    [<InlineData("unit-fact")>]
    [<InlineData("convention")>]
    member _.``Sole unit public erasure refuses withdrawn exact formal premises``(shape: string) =
        let result =
            ClosedCallbackCases.receivingZeroCheck "let callback (value: unit) : unit = value"

        DimensionalCases.noErrors result

        let revision =
            Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish result.Graph
            |> Result.defaultWith (fun errors -> failwithf "%A" errors)

        let entry = revision.Emission.Boundary.ClosedEntries.Values |> Assert.Single
        let formal = entry.Formals |> Assert.Single

        let changed =
            match shape with
            | "convention" ->
                let boundary = revision.Emission.Boundary
                let invocation = boundary.CallbackInvocations[entry.Invocation]

                let invocation =
                    { invocation with
                        Signature =
                            { invocation.Signature with
                                CallingConvention = "not-CDecl"
                            }
                    }

                { revision with
                    Emission =
                        { revision.Emission with
                            Boundary =
                                { boundary with
                                    CallbackInvocations = boundary.CallbackInvocations.Add(entry.Invocation, invocation)
                                }
                        }
                }
            | "type" ->
                let body = revision.Nodes[formal]

                let integer =
                    revision.Nodes.Values
                    |> Seq.find (fun node ->
                        not (Fidelity.PSG.TypeIdentity.isUnit node.Type)
                        && revision.Emission.Numeric.Values.ContainsKey node.Id)

                { revision with
                    Nodes = revision.Nodes.Add(formal, { body with Type = integer.Type })
                }
            | "representation" ->
                { revision with
                    Emission =
                        { revision.Emission with
                            Numeric =
                                { revision.Emission.Numeric with
                                    OccurrenceRepresentations = revision.Emission.Numeric.OccurrenceRepresentations.Remove formal
                                }
                        }
                }
            | _ ->
                { revision with
                    Emission =
                        { revision.Emission with
                            Callable =
                                { revision.Emission.Callable with
                                    UnitNodes = revision.Emission.Callable.UnitNodes.Remove formal
                                }
                        }
                }

        let part, reason =
            if shape = "convention" then
                "Emission.Boundary.CallbackInvocations.Signature",
                "The callback signature differs from its complete nonempty integer-formal CDecl receiving quotation and exact integer or void result."
            else
                "Emission.Boundary.ClosedEntries.UnitParameters",
                "A zero-argument void callback requires its exact sole source unit formal and current unit representation."

        Assert.Contains(Fidelity.PSG.Integrity.check changed, fun issue -> issue.Part = part && issue.Reason = reason)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Process exit extent retains distinct equal registration contexts without synchronous retirement``(anchor: bool) =
        let result =
            ClosedCallbackCases.receivingProcessCheckWith (fun source ->
                let source = source.Replace("    receiveRecord { Handler = FnPtr.ofFunction callback }", "    let entry = { Handler = FnPtr.ofFunction callback }\n    receiveRecord entry\n    receiveRecord entry")
                if anchor then
                    source
                        .Replace("ExitBinding = None", "ExitBinding = Some \"ReceivingCallback.finish\"")
                        .Replace("let callback (u: unit)", "[<FidelityExtern(\"c\", \"normal_exit\")>]\nlet finish (status: int) : unit = NativeDefault.zeroed ()\nlet finishDescriptor: Expr<FunctionDescriptor> = <@ { CName = \"normal_exit\"; Parameters = [| { Name = \"status\"; Type = Integer (Signed, 32); PassBy = Value } |]; ReturnType = Void; CallingConvention = CDecl; OwnershipTransfer = Undeclared } @>\nlet callback (u: unit)")
                else source)
        DimensionalCases.noErrors result
        let scoped = Clef.Compiler.PSGSaturation.SemanticGraph.ScopedDeclarations.read result.Graph
        let activation = scoped.Activations.Values |> Seq.filter(fun row -> match row.Extent with BoundaryCallbackExtent.ProcessExit _ -> true | _ -> false) |> Assert.Single
        Assert.DoesNotContain(activation.Parameter, scoped.Parameters)
        let revision =
            Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish result.Graph
            |> Result.defaultWith (fun errors -> failwithf "%A" errors)
        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let entry = revision.Emission.Boundary.ClosedEntries.Values |> Assert.Single
        let invocation = revision.Emission.Boundary.CallbackInvocations[entry.Invocation]
        match invocation.Extent with
        | Fidelity.PSG.BoundaryCallbackExtent.ProcessExit(selected, status) ->
            Assert.Equal(anchor, selected.IsSome)
            Assert.Equal(0, status)
        | _ -> failwith "A retained registration was classified as synchronous."
        Assert.Equal(2, entry.Registrations.Count)
        let uses = entry.Registrations.Values |> Seq.toList
        Assert.NotEqual<Fidelity.PSG.NodeId list>(uses[0].Context, uses[1].Context)
        Assert.Equal(uses[0].Call, uses[1].Call)
        for use' in uses do
            Assert.Equal(use'.Call, use'.Result)
            Assert.Equal(entry.Formation, use'.Formation)
            Assert.True(Set.isSubset (Set.ofList use'.Context) use'.Participants)
        let numeric = Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project result.Graph |> Result.defaultWith(fun errors -> failwithf "%A" errors)
        for use' in numeric.ForeignResultUses do
            Assert.True(use'.Application.Hypothesis.IsNone)
            Assert.Equal<ForeignResultProofRole list>([ForeignResultProofRole.AbiNarrowing], List.map fst use'.Claims)
            for _,claim in use'.Claims do
                match result.Graph.Nodes[claim].Kind with
                | SemanticKind.Obligation {Body=ObligationBody.IntegerRepresentationCoverage(lo,hi,minimum,maximum)} ->
                    Assert.Equal(-2147483648I,lo)
                    Assert.Equal(2147483647I,hi)
                    Assert.True(minimum<=lo && hi<=maximum)
                | _ -> failwith "Full ABI ingress lost its explicit width embedding obligation."
        let limits: Fidelity.PSG.Binary.Limits =
            { MaxBytes=8*1024*1024; MaxCollectionLength=100000; MaxDepth=128; MaxStringBytes=1024*1024; MaxBigIntegerBytes=4096; MaxValues=2000000 }
        let bytes = Fidelity.PSG.Binary.encode limits revision |> Result.defaultWith(fun error -> failwithf "%A" error)
        let copy = Fidelity.PSG.Binary.decode limits bytes |> Result.defaultWith(fun error -> failwithf "%A" error)
        Assert.Equal(revision.Emission.Boundary, copy.Emission.Boundary)

    [<Theory>]
    [<InlineData("status")>]
    [<InlineData("census")>]
    [<InlineData("result")>]
    [<InlineData("support")>]
    member _.``Process exit public replay refuses changed registration premises``(shape: string) =
        let result = ClosedCallbackCases.receivingProcessCheckWith id
        DimensionalCases.noErrors result
        let revision =
            Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish result.Graph
            |> Result.defaultWith(fun errors -> failwithf "%A" errors)
        let boundary = revision.Emission.Boundary
        let entry = boundary.ClosedEntries.Values |> Assert.Single
        let invocation = boundary.CallbackInvocations[entry.Invocation]
        let changed, suffix, reason =
            if shape="status" then
                let invocation = { invocation with Extent=Fidelity.PSG.BoundaryCallbackExtent.ProcessExit(None, 1) }
                { boundary with CallbackInvocations=boundary.CallbackInvocations.Add(invocation.Identity, invocation) },
                "CallbackInvocations.ProcessExitDeclaration",
                "The process-exit extent differs from its exact immutable status and selected optional anchor declaration."
            else
                let registrations =
                    if shape="census" then Map.empty else
                    entry.Registrations |> Map.map(fun _ use' ->
                        if shape="result" then { use' with Result=entry.Formation }
                        else { use' with Participants=Set.empty })
                let entry={entry with Registrations=registrations}
                let suffix, reason =
                    if shape="census" then "Registrations", "The process-exit registration census differs from its current call and per-application result contexts."
                    elif shape="result" then "RegistrationResult", "The registration differs from its exact receiving application, original formation or signed32 result."
                    else "RegistrationParticipants", "The registration lost its current caller/context dependency support."
                {boundary with ClosedEntries=boundary.ClosedEntries.Add(entry.Formation,entry)}, "ClosedEntries."+suffix, reason
        let changed={ revision with Emission={revision.Emission with Boundary=changed} }
        Assert.Contains(Fidelity.PSG.Integrity.check changed, fun issue -> issue.Part="Emission.Boundary."+suffix && issue.Reason=reason)

    [<Theory>]
    [<InlineData("ExitBinding = None", "ExitBinding = Some \"ReceivingCallback.absent\"", "ProcessExitCallbackDescriptor ExitBinding must resolve one current immutable declaration.")>]
    [<InlineData("SuccessStatus = 0", "SuccessStatus = 2147483648", "ProcessExitCallbackDescriptor requires signed32 SuccessStatus and an explicit optional ExitBinding.")>]
    member _.``Process exit source refuses malformed exact declaration premises``(before: string, after: string, reason: string) =
        let result=ClosedCallbackCases.receivingProcessCheckWith(fun source -> source.Replace(before,after))
        let declarations=Clef.Compiler.PSGSaturation.SemanticGraph.ScopedDeclarations.read result.Graph
        Assert.Contains(declarations.Findings, fun finding -> finding.Message=reason)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``ABI ingress does not manufacture missing behavioral or ABI support``(missingAbi: bool) =
        let result=ClosedCallbackCases.receivingProcessCheckWith id
        DimensionalCases.noErrors result
        let graph=result.Graph
        let numeric=Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project graph |> Result.defaultWith(fun errors -> failwithf "%A" errors)
        let evidence=
            Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.foreignResultApplications graph graph.RangeContextFacts
            |> Result.defaultWith(fun error -> failwithf "%A" error)
            |> List.head
        let changed=
            if missingAbi then {evidence with Abi=None}
            else {evidence with ResultRange=ValueRange.point 0I}
        let models=Clef.Compiler.Baker.Recipes.NumericCarrierRecipes.foreignResultModels graph (numeric.Values.Values |> Seq.toList) changed
        Assert.Equal<ForeignResultProofRole list>([ForeignResultProofRole.LogicalCoverage;ForeignResultProofRole.AbiNarrowing],List.map fst models)
        for _,model in models do
            match Clef.Compiler.Baker.Recipes.NumericCarrierRecipes.foreignResultBody model with
            | ObligationBody.ForeignResultCoverage pending -> Assert.True(pending.Application.Hypothesis.IsNone)
            | _ -> failwith "Absent ABI or behavioral narrowing was replaced with an ingress coverage proof."

    [<Theory>]
    [<InlineData(true,32)>]
    [<InlineData(false,32)>]
    [<InlineData(true,64)>]
    [<InlineData(false,64)>]
    member _.``Complete declared integer ABI ingress preserves signedness width and embedding without behavior``(signed: bool, bits: int) =
        let sign=if signed then "Signed" else "Unsigned"
        let result=ClosedCallbackCases.receivingProcessCheckWith(fun source ->
            source
                .Replace("let scope: Expr<ProcessExitCallbackDescriptor> = <@ { Binding = \"ReceivingCallback.receive\"; Parameter = \"callback\"; ExitBinding = None; SuccessStatus = 0 } @>",
                         "let scope: Expr<ScopedCallbackDescriptor> = <@ { Binding = \"ReceivingCallback.receive\"; Parameter = \"callback\" } @>")
                .Replace("ReturnType = Integer (Signed, 32);", $"ReturnType = Integer ({sign}, {bits});"))
        DimensionalCases.noErrors result
        let graph=result.Graph
        let numeric=Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project graph |> Result.defaultWith(fun errors -> failwithf "%A" errors)
        let expected=if signed then ValueRange.twosComplement bits else ValueRange.unsignedOf bits
        for use' in numeric.ForeignResultUses do
            Assert.True(use'.Application.Hypothesis.IsNone)
            Assert.Equal(expected,numeric.Values[use'.Application.Call].Range)
            Assert.Equal<ForeignResultProofRole list>([ForeignResultProofRole.AbiNarrowing],List.map fst use'.Claims)
        let revision=Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph |> Result.defaultWith(fun errors -> failwithf "%A" errors)
        Assert.Empty(Fidelity.PSG.Integrity.check revision)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``ABI ingress refuses withdrawn declaration or selected target support``(withdrawTarget: bool) =
        let result=ClosedCallbackCases.receivingProcessCheckWith id
        DimensionalCases.noErrors result
        let graph=result.Graph
        let changed=
            if withdrawTarget then {graph with Platform=None} else
            let evidence=Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.foreignResultApplications graph graph.RangeContextFacts |> Result.defaultWith(fun error -> failwithf "%A" error) |> List.head
            let abi=evidence.Abi |> Option.defaultWith(fun () -> failwith "The source ABI premise is absent.")
            let node=graph.Nodes[abi.Node]
            match node.Kind with
            | SemanticKind.RecordExpr(fields,copy) ->
                let fields=fields |> List.filter(fun (name,_) -> name<>"ReturnType")
                {graph with Nodes=graph.Nodes.Add(node.Id,{node with Kind=SemanticKind.RecordExpr(fields,copy);Children=Option.toList copy @ List.map snd fields})}
            | _ -> failwith "The actual ABI descriptor did not retain its source record."
        match Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project changed with
        | Result.Error failures ->
            Assert.Contains(failures,fun failure -> failure.Reason="NumericPublication: Invocation-context range premises changed or the producer receipt is absent; source range settlement is required.")
        | Ok _ -> failwith "A changed declared ABI or target retained its old ingress width proof."
