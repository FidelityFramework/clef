/// Compositional Name Resolution for CCS
/// 
/// This module implements name resolution as a codata/coeffect pattern:
/// - Resolvers are functions from names to bindings (demand-driven)
/// - Open declarations compose resolvers (functional composition)
/// - BCL is structurally impossible (BCL bindings never added)
/// 
/// Key insight: Instead of accumulating bindings in a mutable map,
/// we compose resolver functions. Each `open` declaration adds a new
/// "lens" that tries prefixed lookups before falling back.
module Clef.Compiler.NativeTypedTree.NameResolution

open Clef.Compiler.Syntax
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

// =============================================================================
// Core Types
// =============================================================================

/// Information about an inline function body (for transparent expansion)
type InlineBody = {
    Parameters: string list
    Body: SynExpr
    Range: SourceRange
}

/// Union case info for DU constructor bindings
type UnionCaseInfo = {
    /// The case name (e.g., "IntVal", "FloatVal")
    CaseName: string
    /// The union type this case belongs to
    UnionType: NativeType
    /// Zero-based index of this case in the union (for tag value)
    CaseIndex: int
}

/// A resolved binding - the witness produced by resolution
[<NoComparison; NoEquality>]
type ResolvedBinding = {
    /// The fully qualified name (e.g., "Alloy.Console.Write")
    QualifiedName: string
    /// The binding's type
    Type: NativeType
    /// Whether the binding is mutable
    IsMutable: bool
    /// Reference to the definition node in the semantic graph
    NodeId: NodeId option
    /// For inline functions: body for transparent expansion
    InlineBody: InlineBody option
    /// For DU constructors: case information for proper UnionCase node creation
    UnionCaseInfo: UnionCaseInfo option
    /// For [<Literal>] bindings: compile-time constant value for substitution
    /// When present, VarRef resolution substitutes this value directly at use sites
    NativeLiteral: NativeLiteral option
    /// Whether this binding was defined at module level (top-level)
    /// Module-level bindings are referenced by address, not captured in closures
    /// PRD-14: Critical for correct capture analysis in lambda/lazy expressions
    IsModuleLevel: bool
}

/// A name resolver - codata structure producing bindings on demand
/// 
/// This is the key abstraction: a resolver is a function that,
/// given a name, produces an optional binding. The "codata" perspective
/// means we think of it as something we observe/query, not something
/// we build by accumulation.
type Resolver = string -> ResolvedBinding option

// =============================================================================
// Resolver Combinators
// =============================================================================

/// Empty resolver - resolves nothing
/// This is the identity element for composition
let empty: Resolver = fun _ -> None

/// Singleton resolver - resolves exactly one name
/// Creates a resolver that recognizes only the given name
let singleton (name: string) (binding: ResolvedBinding) : Resolver =
    fun n -> if n = name then Some binding else None

/// Compose resolvers: try first, then second
/// This is how we build up resolution scope - later opens shadow earlier ones
let compose (r1: Resolver) (r2: Resolver) : Resolver =
    fun name ->
        match r1 name with
        | Some b -> Some b
        | None -> r2 name

/// Compose operator (left-biased choice)
let (<|>) = compose

/// Open a namespace: creates resolver that prefixes lookups
/// 
/// When we `open Alloy`, this creates a resolver that:
/// - Takes syntactic name "Console.Write"  
/// - Tries to resolve "Alloy.Console.Write" in the base resolver
/// 
/// This is the key to making BCL impossible: the base resolver only
/// contains source-defined bindings (from Alloy files). There's no
/// BCL in there, so prefixed lookups can only find Alloy bindings.
let openNamespace (ns: string) (baseResolver: Resolver) : Resolver =
    fun name -> baseResolver (ns + "." + name)

/// Open a module with alias: creates resolver that maps alias to full path
/// 
/// Example: `open Alloy.Console as C` would create a resolver where
/// `C.Write` maps to `Alloy.Console.Write`
let openWithAlias (alias: string) (fullPath: string) (baseResolver: Resolver) : Resolver =
    fun name ->
        if name.StartsWith(alias + ".") then
            let suffix = name.Substring(alias.Length + 1)
            baseResolver (fullPath + "." + suffix)
        else
            None

// =============================================================================
// Building Resolvers from Binding Collections
// =============================================================================

/// Create a resolver from a map of bindings
/// This is for bootstrapping from existing binding collections
let fromMap (bindings: Map<string, ResolvedBinding>) : Resolver =
    fun name -> Map.tryFind name bindings

/// Add a binding to a resolver (composes a singleton)
let addBinding (name: string) (binding: ResolvedBinding) (resolver: Resolver) : Resolver =
    compose (singleton name binding) resolver

/// Add multiple bindings to a resolver
let addBindings (bindings: (string * ResolvedBinding) list) (resolver: Resolver) : Resolver =
    bindings |> List.fold (fun r (n, b) -> addBinding n b r) resolver

// =============================================================================
// Resolution with Scope Tracking
// =============================================================================

/// Resolution context - tracks open namespaces for error messages
type ModuleScope = {
    IsNamespace: bool
    RequireQualifiedAccess: bool
}

type ResolutionContext = {
    /// Open namespace prefixes in resolution order (most recent first)
    OpenNamespaces: string list
    /// The base resolver (all registered bindings)
    BaseResolver: Resolver
    /// The composed resolver (base + opens applied)
    ComposedResolver: Resolver
    /// Canonical declaration paths, including modules with no value bindings.
    ModulesAndNamespaces: Map<string, ModuleScope>
    /// Private lexical abbreviations; never exported as module declarations.
    ModuleAliases: Map<string, string>
    /// Current declaration and enclosing paths, nearest first.
    LexicalPaths: string list
}

/// Create initial resolution context with empty scope
let createContext () : ResolutionContext = {
    OpenNamespaces = []
    BaseResolver = empty
    ComposedResolver = empty
    ModulesAndNamespaces = Map.empty
    ModuleAliases = Map.empty
    LexicalPaths = []
}

/// Create context from existing base resolver
let createContextFrom (baseResolver: Resolver) : ResolutionContext = {
    OpenNamespaces = []
    BaseResolver = baseResolver
    ComposedResolver = baseResolver
    ModulesAndNamespaces = Map.empty
    ModuleAliases = Map.empty
    LexicalPaths = []
}

/// Add an open namespace to the context
///
/// Direct bindings (base resolver) always take priority over opens.
/// Among opens, more recent opens take precedence over earlier ones.
let addOpen (ns: string) (ctx: ResolutionContext) : ResolutionContext =
    let newOpenNamespaces = ns :: ctx.OpenNamespaces
    // Recompose: base > opens (most recent first)
    let opensResolver =
        newOpenNamespaces
        |> List.rev  // Apply in original order (earliest first)
        |> List.fold (fun r openNs -> compose (openNamespace openNs ctx.BaseResolver) r) empty
    { ctx with
        OpenNamespaces = newOpenNamespaces
        ComposedResolver = compose ctx.BaseResolver opensResolver }

/// Register a binding in the base resolver
///
/// Direct bindings always take priority over opens. When a Lambda parameter
/// shadows a module-level name (e.g., `sw0` parameter vs `Pins.sw0` from open),
/// the parameter wins because base resolver is checked before open resolvers.
let registerBinding (name: string) (binding: ResolvedBinding) (ctx: ResolutionContext) : ResolutionContext =
    let newBase = addBinding name binding ctx.BaseResolver
    // Recompose: base > opens (opens see the updated base for qualified lookups)
    let opensResolver =
        ctx.OpenNamespaces
        |> List.rev  // Apply in original order
        |> List.fold (fun r ns -> compose (openNamespace ns newBase) r) empty
    { ctx with
        BaseResolver = newBase
        ComposedResolver = compose newBase opensResolver }

/// Names tried by lexical lookup. `global` selects the root table directly.
/// Types and measures use the same paths as expression bindings.
let candidateNames (name: string) (ctx: ResolutionContext) : string list =
    // The parser marks the pseudo-identifier as `global` in LongIdent nodes.
    let rootPrefix =
        ["global."; "`global`."]
        |> List.tryFind (fun prefix -> name.StartsWith(prefix, System.StringComparison.Ordinal))
    if rootPrefix.IsSome then
        [name.Substring(rootPrefix.Value.Length)]
    else
        let head = name.Split('.').[0]
        match Map.tryFind head ctx.ModuleAliases with
        | Some path -> [path + name.Substring(head.Length)]
        | None ->
            let lexical = ctx.LexicalPaths |> List.map (fun ns -> ns + "." + name)
            let opened = ctx.OpenNamespaces |> List.map (fun ns -> ns + "." + name)
            // A local module can shadow a root module. Bare locals still take priority
            // over imported values (including lambda parameters and local bindings).
            if name.Contains('.') then lexical @ [name] @ opened
            else name :: (lexical @ opened)

let addModuleAlias (alias: string) (path: string) (ctx: ResolutionContext) =
    { ctx with ModuleAliases = Map.add alias path ctx.ModuleAliases }

/// Register a declaration path without importing its contents. Prefixes of a
/// dotted declaration denote enclosing namespaces unless already declared.
let registerModule (path: string list) (isNamespace: bool) (qualifiedOnly: bool) (ctx: ResolutionContext) =
    let parents =
        [1 .. path.Length - 1]
        |> List.fold (fun modules count ->
            let name = path |> List.take count |> String.concat "."
            if Map.containsKey name modules then modules
            else Map.add name { IsNamespace = true; RequireQualifiedAccess = false } modules) ctx.ModulesAndNamespaces
    let name = String.concat "." path
    let modules =
        if path.IsEmpty then parents
        else Map.add name { IsNamespace = isNamespace; RequireQualifiedAccess = qualifiedOnly } parents
    { ctx with ModulesAndNamespaces = modules }

let tryResolveModule (name: string) (ctx: ResolutionContext) =
    candidateNames name ctx
    |> List.tryPick (fun path -> ctx.ModulesAndNamespaces |> Map.tryFind path |> Option.map (fun scope -> path, scope))

/// Enter a declaration scope. Enclosing paths permit sibling-qualified access;
/// they do not recursively expose the contents of sibling modules.
let enterModule (path: string list) (ctx: ResolutionContext) : ResolutionContext =
    let paths = [path.Length .. -1 .. 1] |> List.map (fun count -> path |> List.take count |> String.concat ".")
    { ctx with LexicalPaths = paths }

/// Retain canonical exports while restoring the enclosing lexical environment.
/// A declaration's existence in the project is separate from permission to use
/// its short name. Neither local aliases nor opens escape this boundary.
let leaveModule (path: string list) (outer: ResolutionContext) (inner: ResolutionContext) : ResolutionContext =
    let prefix = String.concat "." path + "."
    let exports (name: string) =
        if path.IsEmpty || name.StartsWith(prefix, System.StringComparison.Ordinal) then
            inner.BaseResolver name
        else None
    let newBase = compose exports outer.BaseResolver
    let opens =
        outer.OpenNamespaces
        |> List.rev
        |> List.fold (fun resolver ns -> compose (openNamespace ns newBase) resolver) empty
    { outer with BaseResolver = newBase; ComposedResolver = compose newBase opens
                 ModulesAndNamespaces = inner.ModulesAndNamespaces }

/// Resolve a name using the full composed resolver
let resolve (name: string) (ctx: ResolutionContext) : ResolvedBinding option =
    // A module abbreviation prefixes qualified names; it cannot replace a bare
    // value binding or parameter with the same spelling.
    let local = if name.Contains('.') then None else ctx.BaseResolver name
    local |> Option.orElseWith (fun () -> candidateNames name ctx |> List.tryPick ctx.BaseResolver)

/// Resolve with diagnostics about what was tried
type ResolutionResult =
    | Resolved of ResolvedBinding
    | NotFound of triedPaths: string list

let resolveWithDiagnostics (name: string) (ctx: ResolutionContext) : ResolutionResult =
    // First try exact match via composed resolver
    match resolve name ctx with
    | Some binding -> Resolved binding
    | None ->
        // Collect all paths that were tried for error reporting
        NotFound (candidateNames name ctx)

// =============================================================================
// Invariant Checking (Safety Net)
// =============================================================================

/// BCL namespace prefixes that should NEVER appear
let private bclPrefixes = [
    "System."
    "Microsoft."
    "mscorlib."
    "netstandard."
]

/// Check if a qualified name is BCL (should be impossible in correct system)
let isBclQualifiedName (qualifiedName: string) : bool =
    bclPrefixes |> List.exists qualifiedName.StartsWith

/// Safe resolve - panics if BCL somehow got into the resolver
/// This should NEVER trigger in a correctly constructed system
let resolveSafe (name: string) (ctx: ResolutionContext) : ResolvedBinding option =
    match resolve name ctx with
    | Some binding when isBclQualifiedName binding.QualifiedName ->
        // INVARIANT VIOLATION - BCL should never be in the resolver
        failwithf "INVARIANT VIOLATION: BCL binding '%s' found in resolver. This indicates a bug in binding registration." binding.QualifiedName
    | result -> result
