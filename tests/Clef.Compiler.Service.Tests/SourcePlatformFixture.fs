namespace Clef.Compiler.Service.Tests

open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

/// Source-declared scalar authority shared by target-aware compiler fixtures.
module SourcePlatformFixture =
    let platform : PlatformContext =
        let representation name family bits minimum maximum : NumericRepresentation =
            { Name = name; Capability = "native"; Family = family; Bits = bits
              MinMagnitude = minimum; MaxMagnitude = maximum; Boundary = "wrap" }
        let representations =
            [ representation "octet" "uint" 8 "0" "255"
              representation "signed32" "int" 32 "-2147483648" "2147483647"
              representation "unsigned32" "uint" 32 "0" "4294967295"
              representation "signed64" "int" 64 "-9223372036854775808" "9223372036854775807"
              representation "unsigned64" "uint" 64 "0" "18446744073709551615" ]
        { PlatformLoading = None; PlatformId = "intrinsic-write-test"; Dimensions = Map.ofList ["Pointer",64; "Register",64]
          Representations = representations |> List.map (fun value -> value.Name, value) |> Map.ofList
          EndpointReturns = Map.empty; PlatformLibraryPath = None; PlatformDescription = Some "WriteAuthority.description"
          PlatformArchitecture = None; PlatformOS = None; PlatformSourcePaths = Set.singleton (System.IO.Path.GetFullPath "write-authority.clef")
          Predicates = Map.empty; FreestandingStartup = None; SubstrateKind = None; RuntimeModel = None
          AvailableMemorySpaces = []; DefaultMemorySpace = None; ClockFrequencyMhz = None; NsPerWeightUnit = None; ProjectMemoryPolicy = None }

    let authority =
        let representations = platform.Representations.Values |> Seq.map (fun rep ->
            sprintf "{ Name = %A; Capability = %A; Family = %A; Bits = %d; MinMagnitude = %A; MaxMagnitude = %A; Boundary = %A }"
                rep.Name rep.Capability rep.Family rep.Bits rep.MinMagnitude rep.MaxMagnitude rep.Boundary) |> String.concat "; "
        let template = """module WriteAuthority
type WidthDeclaration = { Name: string; Bits: int }
type Representation = { Name: string; Capability: string; Family: string; Bits: int; MinMagnitude: string; MaxMagnitude: string; Boundary: string }
type TargetCore = { Arch: string; Os: string; Runtime: string; Triple: string; Widths: WidthDeclaration array; Representations: Representation array }
type MemorySpace = { Name: string; Kind: string; Capacity: int; Alignment: int; Granularity: int; Growth: string; Access: string; Base: int option }
type ProgramLifetimeSpaces = { Immutable: string; Mutable: string option }
type Contract = { Floor: int; AtMost: string }
type Endpoint = { Name: string; Location: string; Address: string; Contracts: Contract array }
type BoundarySurface = { Endpoints: Endpoint array }
type PlatformDescription = { Id: string; Core: TargetCore option; Spaces: MemorySpace array; ProgramLifetime: ProgramLifetimeSpaces option; Surfaces: BoundarySurface array }
let rodata = { Name = "rodata"; Kind = "rodata"; Capacity = 4096; Alignment = 16; Granularity = 16; Growth = "fixed"; Access = "r"; Base = None }
let write = { Name = "write"; Location = "syscall-number"; Address = "1"; Contracts = [| { Floor = -4095; AtMost = "count" } |] }
let description = { Id = "intrinsic-write-test"
                    Core = Some { Arch = "x86_64"; Os = "linux"; Runtime = "freestanding"; Triple = "x86_64-unknown-linux-gnu"; Widths = [| { Name = "Pointer"; Bits = 64 }; { Name = "Register"; Bits = 64 } |]; Representations = [| %s |] }
                    Spaces = [| rodata |]; ProgramLifetime = Some { Immutable = "rodata"; Mutable = None }; Surfaces = [| { Endpoints = [| write |] } |] }
"""
        template.Replace("%s", representations)

    let checkResult pointerBits path body =
        let context = { platform with Dimensions = platform.Dimensions.Add("Pointer", pointerBits) }
        let source = authority.Replace("Name = \"Pointer\"; Bits = 64", sprintf "Name = \"Pointer\"; Bits = %d" pointerBits)
        let parse text file =
            match parseStringWithDefaults text file with
            | ParseSuccess input -> input
            | ParseError errors -> failwithf "Parse failed: %A" errors
        checkParsedInputsWithPlatform [parse source "write-authority.clef"; parse body path] (Some context)

    let check pointerBits path body =
        let result = checkResult pointerBits path body
        DimensionalCases.noErrors result
        result.Graph

    /// Exercise the selected project owner, including its captured parsed policy.
    /// The fixture units are real project inputs; no test authors policy authority.
    let checkProjectWithMemoryPolicy model (metadata:(string*string) list) authoritySource source =
        let root = System.IO.Path.GetFullPath(System.IO.Path.Combine(__SOURCE_DIRECTORY__, "../../artifacts/scratch/optional-retirement-projects", System.Guid.NewGuid().ToString("N")))
        System.IO.Directory.CreateDirectory root |> ignore
        let write name (text:string) = System.IO.File.WriteAllText(System.IO.Path.Combine(root,name),text)
        write "Platform.clef" authoritySource
        write "Main.clef" source
        write "Platform.fidproj" "[package]\nname = \"Platform\"\n[compilation]\ntarget = \"cpu\"\n[build]\noutput_kind = \"library\"\nsources = [\"Platform.clef\"]\n[platform]\nruntime_model = \"libc\"\ndescription = \"WriteAuthority.description\"\n"
        let sourcePaths =
            metadata |> List.mapi(fun ordinal (_,text)->let name = $"Metadata{ordinal}.clef" in write name text; name)
        let policy = if model="" then "" else $"memory_model = \"{model}\"\n"
        let sources = sourcePaths@["Main.clef"] |> List.map(fun path->"\""+path+"\"") |> String.concat ", "
        write "App.fidproj" ($"[package]\nname = \"App\"\n[compilation]\ntarget = \"cpu\"\n{policy}[build]\noutput_kind = \"executable\"\nsources = [{sources}]\n[dependencies]\nplatform = {{ path = \"Platform.fidproj\" }}\n")
        Clef.Compiler.Project.ProjectChecker.checkProject(System.IO.Path.Combine(root,"App.fidproj"))
        |> Result.defaultWith(fun failures->failwithf "%A" failures)
        |> _.CheckResult
