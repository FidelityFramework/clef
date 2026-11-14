// SPDX-License-Identifier: MIT
// Declared kernel transport is an external input domain, never a call site.
module Clef.Compiler.Baker.Recipes.KernelDeclarations

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Platform = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution
module Boundary = Clef.Compiler.Baker.Ingredients.Boundaries

type private ResultBuilder() =
    member _.Bind(value, next) = Result.bind next value
    member _.Return(value) = Ok value
    member _.ReturnFrom(value: Result<'T, 'E>) = value
    member _.Zero() = Ok ()
    member _.Delay(f: unit -> Result<'T, 'E>) = f
    member _.Run(f: unit -> Result<'T, 'E>) = f ()
    member _.Combine(first: Result<unit, 'E>, second: unit -> Result<'T, 'E>) =
        match first with
        | Ok () -> second ()
        | Error err -> Error err
    member _.For(items: seq<'T>, body: 'T -> Result<unit, 'E>) =
        use enumerator = items.GetEnumerator()
        let rec loop () =
            if not (enumerator.MoveNext()) then Ok ()
            else
                match body enumerator.Current with
                | Ok () -> loop ()
                | Error err -> Error err
        loop ()

let private result = ResultBuilder()

let private mapResult (fn: 'T -> Result<'U, 'E>) (items: 'T list) : Result<'U list, 'E> =
    let rec loop acc remaining =
        match remaining with
        | [] -> Ok (List.rev acc)
        | head :: tail ->
            match fn head with
            | Ok value -> loop (value :: acc) tail
            | Error err -> Error err
    loop [] items

// Preserve the checker's nominal key for the canonical namespace declaration.
// Comparing only a display name would also admit unrelated KernelTarget types.
let targetIdentity : NominalTypeIdentity =
    { Module=["Fidelity";"Platform";"Contracts"]; Name="Platform.Contracts.KernelTarget" }

let row (ingress: KernelIngress) =
    { Class=EdgeClass.Spatial; Role=EdgeRole.KernelIngress ingress; Ordinal=0
      Sources=Set.toList ingress.Participants; Target=ingress.Site }

let private uses (graph: SemanticGraph) path =
    graph.Nodes |> Map.toSeq |> Seq.choose (fun (id,node) ->
        if node.IsReachable && (Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence node |> List.exists (fun edge -> edge.Sources |> List.exists (fun source -> Set.contains source path))) then
            Some(id,(Boundary.premise node).Shape)
        else None) |> Map.ofSeq

let private declaration (graph: SemanticGraph) (site: SemanticNode) =
    let mutable participants = Set.singleton site.Id
    let require condition reason = if condition then Ok () else Error reason
    let node id =
        participants <- participants.Add id
        match graph.Nodes.TryFind id with
        | Some found -> Ok found
        | None -> Error "A kernel ingress participant is absent."
    let rec resolve seen id =
        result {
            do! require (not(Set.contains id seen)) "The kernel ingress declaration is cyclic."
            let! current = node id
            let seen = Set.add id seen
            match current.Kind,current.Children with
            | SemanticKind.TypeAnnotation(inner,_),_ | SemanticKind.Quote(inner,_),_
            | SemanticKind.VarRef(_,Some inner),_ -> return! resolve seen inner
            | SemanticKind.Binding(_,false,_,_),[inner] -> return! resolve seen inner
            | _ -> return current
        }
    let value id = resolve Set.empty id
    let rec retain seen id =
        result {
            if not(Set.contains id seen) then
                let! current = node id
                let seen = Set.add id seen
                let references = match current.Kind with SemanticKind.VarRef(_,Some target) -> [target] | _ -> []
                for child in (current.Children @ references) do
                    do! retain seen child
        }
    let fields id =
        result {
            let! resolved = value id
            match resolved.Kind with
            | SemanticKind.RecordExpr(fields,None) -> return fields
            | _ -> return! Error "A kernel ingress requires complete source records."
        }
    let field name fields =
        match fields |> List.filter (fst >> (=) name) with
        | [_,id] -> Ok id
        | _ -> Error $"Kernel transport requires exactly one '{name}' declaration."
    let text id =
        result {
            let! resolved = value id
            match resolved.Kind with
            | SemanticKind.Literal(NativeLiteral.String value) -> return value
            | _ -> return! Error "Kernel transport representation names must be source string literals."
        }
    let parseBigInt (raw: string) =
        match System.Numerics.BigInteger.TryParse raw with
        | true, parsed -> Ok parsed
        | false, _ -> Error $"Invalid integer magnitude '{raw}' in kernel transport representation."
    result {
        let! parentNodeOpt =
            match site.Parent with
            | Some parentId -> node parentId |> Result.map Some
            | None -> Ok None
        let! scope =
            match parentNodeOpt with
            | Some {Id=id;Kind=SemanticKind.ModuleDef _} -> Ok id
            | _ -> Error "Kernel ingress requires the declaration's actual module scope."
        let! siteFields = fields site.Id
        let! compute = field "Compute" siteFields
        let before = participants
        let! implementation = value compute
        let computePath = Set.difference participants before |> Set.add compute |> Set.add implementation.Id
        let! parameters,resultId =
            match implementation.Kind with
            | SemanticKind.Lambda(parameters,resultId,[],_,_) when parameters.Length=2 ->
                Ok (parameters |> List.map (fun (name,_,id) -> name,id),resultId)
            | _ -> Error "Kernel ingress requires one capture-free declaration with exactly two scalar formals."
        let! implParentOpt =
            match implementation.Parent with
            | Some parentId -> node parentId |> Result.map Some
            | None -> Ok None
        let! binding =
            match implParentOpt with
            | Some {Id=id;Kind=SemanticKind.Binding(_,false,_,_)} -> Ok id
            | _ -> Error "Kernel ingress requires the immutable Compute binding identity."
        let ordinaryCalls = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolve graph
        do! require (ordinaryCalls.Calls.Values |> Seq.forall (fun call -> call.Targets |> List.forall (fun target -> target.Lambda<>implementation.Id)))
                "Kernel Compute reused by ordinary calls requires a joint input domain and transport instantiation contract; this ingress cannot replace ordinary actual ranges."
        let computeUses = uses graph computePath
        do! require (computeUses |> Map.forall (fun useSite shape -> shape.Form="module" || participants.Contains useSite))
                "Kernel Compute used outside its declaration path requires a callable/transport instantiation contract."
        for (_, paramId) in parameters do
            let! _ = node paramId
            ()
        let! _ = node resultId
        let targets = graph.Nodes.Values |> Seq.filter (fun candidate ->
            match candidate.Kind,candidate.Type with
            | SemanticKind.Binding(_,false,_,_),NativeType.TApp(constructor,_) ->
                NominalTypeIdentity.ofConstructor constructor=targetIdentity && Platform.isSelectedPlatformDeclaration graph candidate
            | _ -> false) |> Seq.toList
        let! target =
            match targets with
            | [target] -> Ok target
            | _ -> Error "Exactly one selected Fidelity.Platform.Contracts.KernelTarget must declare kernel transport."
        let! targetFields = fields target.Id
        let reading = Platform.read graph
        do! require reading.Findings.IsEmpty "The selected kernel core declaration is invalid."
        let! core =
            match reading.Platform |> Option.bind _.Core with
            | Some core -> Ok core
            | None -> Error "Kernel transport requires an explicit selected instruction core."
        do! retain Set.empty core.Node
        let transport name =
            result {
                let selected = core.Representations |> List.filter (fun item -> item.Representation.Name=name)
                let! declared =
                    match selected with
                    | [declared] -> Ok declared
                    | _ -> Error $"Kernel transport representation '{name}' is absent or duplicated in the selected core."
                // Retain the complete selected representation record, including
                // every literal defining its decoder, rather than only its name.
                do! retain Set.empty declared.Node
                let representation = declared.Representation
                do! require (representation.Capability="native" && representation.Bits>0) "The kernel transport requires a declared native scalar decoder."
                let! capacity =
                    match representation.Family with
                    | "int" -> Ok (ValueRange.twosComplement representation.Bits)
                    | "uint" -> Ok (ValueRange.unsignedOf representation.Bits)
                    | _ -> Error "This kernel transport admits explicit signed or unsigned integer decoders."
                let! minMag = parseBigInt representation.MinMagnitude
                let! maxMag = parseBigInt representation.MaxMagnitude
                let range = ValueRange.bounded minMag maxMag
                do! require (range=capacity) "A restricted kernel input domain requires an explicit validation contract; representation capacity alone cannot assert it."
                return {Declaration=declared.Node;Representation=representation;Range=range}
            }
        let! inputsFieldId = field "Inputs" targetFields
        let! inputsNode = value inputsFieldId
        let! inputs =
            match inputsNode.Kind with
            | SemanticKind.ArrayExpr names ->
                names |> mapResult (fun nameId ->
                    result {
                        let! repName = text nameId
                        return! transport repName
                    })
            | _ -> Error "KernelTarget.Inputs requires an ordered source array of representation names."
        do! require (inputs.Length=parameters.Length) "Kernel transport input order must correspond exactly to the Compute formals."
        let! resultFieldId = field "Result" targetFields
        let! resultRepName = text resultFieldId
        let! output = transport resultRepName
        return {Site=site.Id;Scope=scope;Target=target.Id;Core=core.Node;ComputeBinding=binding;Implementation=implementation.Id
                ComputePath=computePath;Uses=computeUses
                Parameters=parameters;Result=resultId;Inputs=inputs;Output=output;Participants=participants
                Premises=participants |> Seq.map (fun id -> id,(Boundary.premise graph.Nodes[id]).Shape) |> Map.ofSeq
                SourceFiles=participants |> Seq.map (fun id -> id,graph.Nodes[id].Range.File) |> Map.ofSeq
                Platform=Boundary.platformPremise graph.Platform}
    }

let elaborate (graph: SemanticGraph) =
    graph.Nodes.Values |> Seq.choose (fun site ->
        match site.Kind with
        | SemanticKind.Binding(_,false,_,Some DeclRoot.KernelModule) -> Some(site.Id,declaration graph site)
        | _ -> None) |> Map.ofSeq

// Correspondence of the held transport DTO to captured literal declarations.
// This validates the existing construction; it neither selects a carrier nor
// substitutes representation capacity for a computed value range.
let private transportFactsAgree (ingress: KernelIngress) =
    let fact id=ingress.Premises.TryFind id
    let rec resolve seen id =
        if Set.contains id seen then None else
        match fact id with
        | Some value when value.Form="binding" || value.Form="annotation" || value.Form="quotation" ->
            match value.Children with [child] -> resolve (Set.add id seen) child | _ -> None
        | Some value when value.Form="reference" ->
            match value.References with [target] -> resolve (Set.add id seen) target | _ -> None
        | value -> value
    let field id name =
        match resolve Set.empty id with
        | Some value when value.Form="record" && value.Text.Length=value.Children.Length ->
            match List.zip value.Text value.Children |> List.filter (fst >> (=) name) with [_,child] -> Some child | _ -> None
        | _ -> None
    let text id = match resolve Set.empty id with Some {Form="string";Text=[value]} -> Some value | _ -> None
    let number id = match resolve Set.empty id with Some {Form=("integer"|"unsigned-integer");Numbers=[value]} -> Some value | _ -> None
    let fieldText id name=field id name |> Option.bind text
    let transport (value: KernelTransport) =
        let representation=value.Representation
        let expected=["Name",representation.Name;"Capability",representation.Capability;"Family",representation.Family
                      "MinMagnitude",representation.MinMagnitude;"MaxMagnitude",representation.MaxMagnitude;"Boundary",representation.Boundary]
        let lower=System.Numerics.BigInteger.TryParse representation.MinMagnitude
        let upper=System.Numerics.BigInteger.TryParse representation.MaxMagnitude
        (expected |> List.forall (fun (name,text) -> fieldText value.Declaration name=Some text)) &&
        (field value.Declaration "Bits" |> Option.bind number)=Some(bigint representation.Bits) &&
        (match lower,upper with (true,lower),(true,upper) -> value.Range=ValueRange.bounded lower upper | _ -> false)
    let inputNames = field ingress.Target "Inputs" |> Option.bind (fun id -> resolve Set.empty id) |> Option.bind (fun value ->
        if value.Form<>"array" then None else
        let names=value.Children |> List.map text
        if names |> List.exists Option.isNone then None else Some(List.choose id names))
    inputNames=Some(ingress.Inputs |> List.map _.Representation.Name) &&
    fieldText ingress.Target "Result"=Some ingress.Output.Representation.Name &&
    (ingress.Inputs @ [ingress.Output] |> List.forall transport) &&
    (match fact ingress.Implementation with
     | Some implementation -> implementation.Form="lambda" && implementation.Parent=Some ingress.ComputeBinding &&
                              implementation.Children=((ingress.Parameters |> List.map snd) @ [ingress.Result])
     | None -> false) &&
    (fact ingress.Site |> Option.exists (fun site -> site.Parent=Some ingress.Scope))

// Passive exact-premise read. Missing/stale transport grants no range facts.
let read (graph: SemanticGraph) site =
    let rows =
        graph.Edges
        |> List.choose (fun edge ->
            match edge.Role with
            | EdgeRole.KernelIngress ingress when ingress.Site=site -> Some(edge, ingress)
            | _ -> None)
    match rows with
    | [edge, ingress] ->
        let current=ingress.Participants |> Seq.choose (fun id -> graph.Nodes.TryFind id |> Option.map (fun node -> id,(Boundary.premise node).Shape)) |> Map.ofSeq
        let files=ingress.Participants |> Seq.choose (fun id -> graph.Nodes.TryFind id |> Option.map (fun node -> id,node.Range.File)) |> Map.ofSeq
        let expected=row ingress
        if edge.Class=expected.Class && edge.Role=expected.Role && edge.Ordinal=expected.Ordinal && edge.Sources=expected.Sources && edge.Target=expected.Target &&
           current=ingress.Premises && files=ingress.SourceFiles && ingress.Platform=Boundary.platformPremise graph.Platform &&
           ingress.Uses=uses graph ingress.ComputePath && transportFactsAgree ingress then Ok ingress
        else Error "Kernel ingress declaration, ordered formals, transport or source authority changed; source normalization is required."
    | _ -> Error "Exactly one source kernel ingress row is required."

let admitted (graph: SemanticGraph) =
    graph.Nodes.Values |> Seq.choose (fun node ->
        match node.Kind with
        | SemanticKind.Binding(_,false,_,Some DeclRoot.KernelModule) ->
            match read graph node.Id with
            | Ok ingress -> Some ingress
            | Error _ -> None
        | _ -> None) |> Seq.toList

let seeds graph =
    admitted graph |> List.collect (fun ingress -> List.zip ingress.Parameters ingress.Inputs |> List.map (fun ((_,formal),transport) -> formal,transport.Range)) |> Map.ofList
