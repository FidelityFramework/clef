/// Device access plans are checked once in CCS; lowering consumes their evidence.
module Clef.Compiler.PSGSaturation.SemanticGraph.DeviceAccess

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.Expressions.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.PSGSaturation.SemanticGraph.Mmio

exception private InvalidDeclaration of NodeId * string

type private Register = {
    Node: NodeId
    Name: string
    Region: NodeId
    Offset: bigint
    Bits: bigint
    Access: Set<char>
    ByteOrder: string
    Ordering: string
}

type private Grant = {
    Node: NodeId
    Name: string
    MappingNode: NodeId
    MappingName: string
    Region: NodeId
    RegionName: string
    Space: DeclaredSpace
    AddressSpace: string
    RegionAddressSpace: string
    Base: bigint option
    Lifetime: string
    Establishment: string
    Premises: string list
    Access: Set<char>
    Registers: Register list
    Predicates: PredicateEvidence list
}

let private invalid id message = raise (InvalidDeclaration(id, message))
let private require id message value = value |> Option.defaultWith (fun () -> invalid id message)
let private ensure id message valid = if not valid then invalid id message

let private record graph kind id =
    match Predicates.valueOf graph id with
    | Some node when typeName node = Some kind ->
        match node.Kind with
        | SemanticKind.RecordExpr(fields, _) -> node.Id, fields
        | _ -> invalid id (kind + " must be an immutable record declaration")
    | _ -> invalid id (kind + " must be an immutable record declaration")

let private memberId id fields name = field name fields |> require id ("Missing declaration field " + name)
let private staticString graph id =
    match Predicates.valueOf graph id with
    | Some { Kind = SemanticKind.Literal(NativeLiteral.String value) } -> Some value
    | _ -> None
let private text graph id fields name =
    match memberId id fields name |> Predicates.valueOf graph with
    | Some { Kind = SemanticKind.Literal(NativeLiteral.String value) } when value <> "" -> value
    | _ -> invalid id (name + " must be a nonempty literal string")
let private number graph id fields name =
    memberId id fields name |> Predicates.integerOf graph |> require id (name + " must be a closed integer declaration")
let private array graph id fields name =
    match memberId id fields name |> Predicates.valueOf graph with
    | Some { Kind = SemanticKind.ArrayExpr elements } -> elements
    | _ -> invalid id (name + " must be a literal array")
let private permissions id (access: string) =
    ensure id "Device access must be r, w, or rw" (List.contains access ["r"; "w"; "rw"])
    Set.ofSeq access
let private distinct id kind names =
    ensure id ("Duplicate " + kind + " in device access plan") ((Set.ofList names).Count = names.Length)

let private readGrant graph platform id =
    let id, fields = record graph "DeviceGrant" id
    let mappingId, mapping = memberId id fields "Mapping" |> record graph "DeviceMapping"
    let regionId, region = memberId mappingId mapping "Region" |> record graph "DeviceRegion"
    let spaceId, _ = memberId regionId region "Space" |> record graph "MemorySpace"
    let space = platform.Spaces |> List.tryFind (fun s -> s.Node = spaceId)
                |> require regionId "Device region must cite a MemorySpace in the selected platform description"
    ensure regionId "MMIO requires a positive fixed peripheral/register space" (space.Capacity > 0L && space.Growth = "fixed" && List.contains space.Kind ["peripheral"; "registers"])
    ensure regionId "Device region alignment and granularity must be positive" (space.Alignment > 0 && space.Granularity > 0)
    let baseAddress =
        match memberId mappingId mapping "Base" |> Predicates.valueOf graph with
        | Some { Kind = SemanticKind.UnionCase("None", _, _) }
        | Some { Kind = SemanticKind.DUConstruct("None", _, _, _) } -> None
        | Some { Kind = SemanticKind.UnionCase("Some", _, Some value) }
        | Some { Kind = SemanticKind.DUConstruct("Some", _, Some value, _) } ->
            Some(Predicates.integerOf graph value |> require mappingId "Mapping Base must be None or Some closed integer")
        | _ -> invalid mappingId "Mapping Base must be None or Some closed integer"
    let register value =
        let rid, rf = record graph "DeviceRegister" value
        let rregion, _ = memberId rid rf "Region" |> record graph "DeviceRegion"
        let r = {
            Node = rid; Name = text graph rid rf "Name"; Region = rregion
            Offset = number graph rid rf "Offset"; Bits = number graph rid rf "TransactionBits"
            Access = text graph rid rf "Access" |> permissions rid
            ByteOrder = text graph rid rf "ByteOrder"; Ordering = text graph rid rf "Ordering" }
        ensure rid "Register and mapping must cite the same DeviceRegion declaration" (r.Region = regionId)
        ensure rid "Register transaction width must be a positive multiple of eight bits" (r.Bits > 0I && r.Bits % 8I = 0I)
        ensure rid "Register transaction lies outside its region" (r.Offset >= 0I && r.Offset + r.Bits / 8I <= bigint space.Capacity)
        ensure rid "Register permissions exceed its region" (Set.isSubset r.Access (permissions regionId space.Access))
        r
    let predicate value =
        let pid, pf = record graph "ClefPredicate" value
        let expression = memberId pid pf "Condition"
        // Do not accept an executable bool in place of phase-distinct syntax.
        let rec isQuote seen node =
            if Set.contains node seen then false else
            let seen = Set.add node seen
            match SemanticGraph.tryGetNode node graph with
            | Some { Kind = SemanticKind.Quote(_, true) } -> true
            | Some { Kind = SemanticKind.TypeAnnotation(inner, _) } -> isQuote seen inner
            | Some { Kind = SemanticKind.VarRef(_, Some binding) } ->
                match SemanticGraph.tryGetNode binding graph with
                | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> isQuote seen value
                | _ -> false
            | _ -> false
        ensure pid "A ClefPredicate Condition must be a typed quotation" (isQuote Set.empty expression)
        Predicates.condition graph (text graph pid pf "Name") pid expression (text graph pid pf "Source")
    let registers = array graph id fields "Registers" |> List.map register
    let predicates = array graph id fields "Predicates" |> List.map predicate
    distinct id "register name" (registers |> List.map (fun r -> r.Name))
    distinct id "predicate name" (predicates |> List.map (fun p -> p.Name))
    let access = text graph id fields "Access" |> permissions id
    ensure id "Grant permissions exceed its region" (Set.isSubset access (permissions regionId space.Access))
    { Node = id; Name = text graph id fields "Name"; MappingNode = mappingId
      MappingName = text graph mappingId mapping "Name"; Region = regionId; RegionName = space.Name; Space = space
      AddressSpace = text graph mappingId mapping "AddressSpace"; RegionAddressSpace = text graph regionId region "AddressSpace"
      Base = baseAddress; Lifetime = text graph mappingId mapping "Lifetime"; Establishment = text graph mappingId mapping "Establishment"
      Premises = [text graph regionId region "Source"; text graph mappingId mapping "Source"]
      Access = access; Registers = registers; Predicates = predicates }

/// Settle at the concrete access boundary, after ranges and curry have settled.
/// Composer receives these facts and does not rediscover declarations.
let settle (sourceDiagnostics: Diagnostic list) (graph: SemanticGraph) : Map<NodeId, MmioAccessEvidence> * Diagnostic list =
    let mutable diagnostics = []
    let report id code message related =
        let node = graph.Nodes.[id]
        diagnostics <- { Severity = NativeDiagnosticSeverity.Error; Code = code; Message = message
                         Range = node.Range; RelatedNodes = id :: related; Reachability = ReachabilityContext.Unknown } :: diagnostics
    let plans = graph.Nodes.Values |> Seq.filter (fun node ->
        match node.Kind with SemanticKind.RecordExpr _ -> typeName node = Some "DeviceAccessPlan" | _ -> false) |> Seq.toList
    let platform = (read graph).Platform
    let mutable planName = ""
    let mutable grants = []
    try
        match plans with
        | [] -> () // Existing raw-address programs remain explicitly unbound.
        | [plan] ->
            let platform = platform |> require plan.Id "A device access plan requires a selected platform description"
            let id, fields = record graph "DeviceAccessPlan" plan.Id
            planName <- text graph id fields "Name"
            grants <- array graph id fields "Grants" |> List.map (readGrant graph platform)
            distinct id "grant name" (grants |> List.map (fun g -> g.Name))
            // Reuse BAREWire's layout rules, including power-of-two alignment
            // and overlap, for granted spaces in each declared address space.
            for addressSpace, group in grants |> List.groupBy (fun g -> g.RegionAddressSpace) do
                let spaces = group |> List.map (fun g -> g.Space) |> List.distinctBy (fun s -> s.Node) |> List.map memorySpace |> List.toArray
                let projection: BAREWire.Platform.PlatformDescription = {
                    Id = planName; DisplayName = planName; Substrate = "cpu"; Core = None
                    Spaces = spaces; Surfaces = [||]; Buffers = [||]; Transports = [||]; Notes = [||]; Limits = [||]
                    Lifecycle = { Clocks = [||]; Resets = [||]; Entry = "mmio"; Teardown = ""; Persistence = "volatile" }
                }
                let findings = BAREWire.Platform.Check.run projection
                ensure id (sprintf "BAREWire device-region layout in %s: %A" addressSpace findings) (findings.Length = 0)
        | _ :: second :: _ -> invalid second.Id "Exactly one DeviceAccessPlan may be selected"
    with InvalidDeclaration(id, message) -> report id DiagnosticCodes.CCS8209_DeviceAccessDeclaration message []
    let core = platform |> Option.bind (fun p -> p.Core)
    let pointerBits = core |> Option.bind (fun c -> c.Widths |> List.tryFind (fun w -> w.Name = "Pointer")) |> Option.map (fun w -> w.Bits)
    let endian = core |> Option.bind (fun c -> recordOf graph c.Node) |> Option.bind (fun (_, fields) -> field "Endianness" fields) |> Option.bind (stringOf graph)
    let constructors = System.Collections.Generic.Dictionary<NodeId, MmioAccessEvidence * Set<char>>()
    let constructor id (op: string) args =
        match constructors.TryGetValue id with
        | true, value -> value
        | _ ->
            let bound = op.StartsWith("bind", System.StringComparison.Ordinal)
            let bits = int (op.Substring(if bound then 4 else 3))
            let pointer = pointerBits |> require id "MMIO needs the declared Pointer width"
            ensure id "MMIO lowering currently supports 32-bit and 64-bit pointers" (pointer = 32 || pointer = 64)
            let binding, address, access =
                if bound then
                    let grantName, registerName =
                        match args with
                        | [g; r] -> staticString graph g |> require id "MMIO grant name must be static", staticString graph r |> require id "MMIO register name must be static"
                        | _ -> invalid id "MMIO binding requires a grant name and a register name"
                    let grant = grants |> List.tryFind (fun g -> g.Name = grantName) |> require id ("MMIO grant is not in the selected plan: " + grantName)
                    let register = grant.Registers |> List.tryFind (fun r -> r.Name = registerName) |> require id ("MMIO register is not granted: " + registerName)
                    let declarationNodes = [plans.Head.Id; grant.Node; grant.MappingNode; grant.Region; grant.Space.Node; register.Node]
                    let dependencies = declarationNodes @ (grant.Predicates |> List.collect (fun p -> p.Declaration :: p.Expression :: p.Dependencies)) |> Set.ofList
                    let overlaps (a: SourceRange) (b: SourceRange) =
                        a.File <> "" && a.File = b.File &&
                        (a.Start.Line, a.Start.Column) <= (b.End.Line, b.End.Column) &&
                        (b.Start.Line, b.Start.Column) <= (a.End.Line, a.End.Column)
                    let typeError = sourceDiagnostics |> List.tryFind (fun diagnostic ->
                        diagnostic.Severity = NativeDiagnosticSeverity.Error &&
                        (diagnostic.RelatedNodes |> List.exists (fun n -> Set.contains n dependencies) ||
                         dependencies |> Seq.exists (fun n -> overlaps graph.Nodes.[n].Range diagnostic.Range)))
                    match typeError with
                    | Some diagnostic -> invalid id ("MMIO source declaration contains a type error: " + diagnostic.Message)
                    | None -> ()
                    ensure id "MMIO accessor width disagrees with the register transaction requirement" (register.Bits = bigint bits)
                    ensure id "MMIO byte order is unsupported or disagrees with the platform" (endian = Some "little" && register.ByteOrder = "little")
                    ensure id "MMIO ordering requirement is unsupported; volatile does not supply a fence" (register.Ordering = "volatile")
                    ensure id "MMIO mapping lifetime is pending; only image-lifetime bindings can be lowered" (grant.Lifetime = "image")
                    let baseAddress = grant.Base |> require id "MMIO mapping base is pending; a runtime mapping has not been established"
                    ensure id "MMIO mapping establishment is pending or unsupported" (List.contains grant.Establishment ["reset-identity"; "boot-contract"])
                    if grant.Establishment = "reset-identity" then
                        ensure id "Reset identity mapping disagrees with its region base/address space" (grant.AddressSpace = grant.RegionAddressSpace && grant.Space.Base |> Option.map bigint = Some baseAddress)
                    ensure id "MMIO mapping extent lies outside the platform address space" (baseAddress > 0I && baseAddress + bigint grant.Space.Capacity <= (1I <<< pointer))
                    ensure id "MMIO mapping base is misaligned for its region" (baseAddress % bigint grant.Space.Alignment = 0I)
                    ensure id "MMIO transaction violates region granularity" (register.Offset % bigint grant.Space.Granularity = 0I && bigint (bits / 8) % bigint grant.Space.Granularity = 0I)
                    for predicate in grant.Predicates do
                        ensure id (sprintf "MMIO predicate '%s' is %A: %s" predicate.Name predicate.Status predicate.Message) (predicate.Status = Established)
                    let evidence = {
                        Plan = planName; Grant = grant.Name; Register = register.Name; Region = grant.RegionName
                        Mapping = grant.MappingName; AddressSpace = grant.AddressSpace
                        DeclarationNodes = declarationNodes
                        Predicates = grant.Predicates
                        Premises = ("mapping establishment: " + grant.Establishment) :: grant.Premises }
                    Some evidence, baseAddress + register.Offset, Set.intersect grant.Access register.Access
                else
                    ensure id "Raw MMIO address construction is forbidden by the selected device access plan" plans.IsEmpty
                    let address = match args with [address] -> Predicates.integerOf graph address |> require id "MMIO address must be a statically declared integer" | _ -> invalid id "MMIO constructor requires one address"
                    None, address, Set.ofList ['r'; 'w']
            ensure id "MMIO address is null, outside the platform address space, or misaligned" (address > 0I && address + bigint (bits / 8) <= (1I <<< pointer) && address % bigint (bits / 8) = 0I)
            let evidence = { Operation = op; Address = address; Bits = bits; Binding = binding }
            constructors.Add(id, (evidence, access))
            evidence, access
    let mutable evidence = Map.empty
    for node in graph.Nodes.Values do
        if node.IsReachable then
            match operation graph node.Id with
            | None -> ()
            | Some(op, args) ->
                try
                    let result =
                        if op.StartsWith("reg") || op.StartsWith("bind") then fst (constructor node.Id op args)
                        else
                            let isRead = op.StartsWith("read")
                            let bits = int (op.Substring(if isRead then 4 else 5))
                            ensure node.Id "Invalid MMIO accessor arity" (args.Length = if isRead then 1 else 2)
                            let handle = Predicates.valueOf graph args.Head |> require node.Id "MMIO handle provenance is pending; an immutable concrete binding is required"
                            let origin, originArgs = operation graph handle.Id |> require node.Id "MMIO handle provenance is pending; an immutable concrete binding is required"
                            ensure node.Id "MMIO handle must originate at a register constructor" (origin.StartsWith("reg") || origin.StartsWith("bind"))
                            let handleEvidence, access = constructor handle.Id origin originArgs
                            ensure node.Id "MMIO access width does not match its opaque register handle" (handleEvidence.Bits = bits)
                            ensure node.Id ("MMIO " + (if isRead then "read" else "write") + " is not permitted by the register and grant") (Set.contains (if isRead then 'r' else 'w') access)
                            if not isRead then
                                let range = graph.Nodes.[args.[1]].ValueRange |> Option.defaultValue ValueRange.Unbounded
                                let fits =
                                    match ValueRange.endpoints range with
                                    | Some(ValueRange.Endpoint.Finite lo, ValueRange.Endpoint.Finite hi) -> lo >= 0I && hi < (1I <<< bits)
                                    | _ -> false
                                ensure node.Id "MMIO write value is not proven within the unsigned register width" fits
                            { handleEvidence with Operation = op }
                    evidence <- Map.add node.Id result evidence
                with InvalidDeclaration(id, message) -> report id DiagnosticCodes.CCS8210_DeviceAccessUnestablished message [node.Id]
    evidence, List.rev diagnostics
