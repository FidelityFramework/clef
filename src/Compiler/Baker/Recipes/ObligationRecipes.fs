// SPDX-License-Identifier: MIT

/// Baker Recipes -- Obligations.
///
/// How the ingredients combine for each obligation family. Each recipe takes
/// its subject and returns the Enrichment that states the obligation over it:
/// the node, the hyperedge whose source set is the structure constrained, and,
/// where a declaration governs the subject, the residence edge from it.
///
/// This is the crossing Obligation_Residency 3 names, "from analysis to
/// enrichment". What Composer's ProofObligations coeffect observed from beside
/// the graph is minted here, in it, at saturation (C-01 14.5). Both dispatches
/// read the result; nothing below the graph authors an obligation.
///
/// Families, all of callsheet standing "generated":
///   storage-reservation, view-containment, terminator-sentinel   per literal
///   memory-map-disjointness                                       all literals, cites rodata
///   concat-copy-bound                                             per String.concat2 site
///   buffer-capacity, input-buffer-bound, input-copy-bound         the readln site, cites consoleReadln
///
/// The last row retires two of HelloProof's five recorded leaks. `read_bound`
/// and `read_copy_bound` existed only build-time because the 1024 lived in
/// pSysReadline; here they are graph-born, citing the declaration, and the
/// site carries the capacity as the annotation the lowering reads.
module Clef.Compiler.Baker.Recipes.ObligationRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.DimensionAlgebra
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution
open Clef.Compiler.Baker.Ingredients.Obligations

/// This conditional arithmetic theorem starts after the native guards. It does
/// not establish the driver's allocation extent, multiplication correctness,
/// callback retirement, or disjointness between workers.
let mappedElementSpan enrichId (site: SemanticNode) (sources: NodeId list) (model: MappedSpanModel) : Enrichment =
    let node = obligationNode site enrichId
                   { Id = (let (NodeId value) = site.Id in sprintf "mapped_element_span_%d" value); Kind = "mapped-element-span"; Logic = "QF_LIA"
                     Statement = sprintf "After native mapping guards establish a positive byte extent <= %A, divisible by %d, and an aligned nonwrapping base, every checked element index denotes a complete %d-byte span inside that extent with %d-byte element alignment. Native extent provenance, stride*rows checks, scoped retirement and worker disjointness are separate contracts; this theorem proves only the additive/index span step."
                                         model.MaximumExtent model.ElementBytes model.ElementBytes model.ElementAlignment
                     Source = fmtRange site.Range; Refs = ["CWE-125"; "CWE-787"; "CWE-190"]
                     Body = ObligationBody.MappedElementSpan model }
    { NewNodes = [node]; NewEdges = [constrains (site.Id :: sources |> List.distinct) node]; Annotated = [] }

/// Retain the analysed enclosure as evidence; do not replace it with a point
/// computed here, which would conceal a broken range-analysis result.
let integerLiteral (enrichId: int) (name: string) (site: SemanticNode) (value: bigint) (lower: bigint) (upper: bigint) : Enrichment =
    let node = obligationNode site enrichId
                   { Id = name; Kind = "integer-literal-range"; Logic = "QF_LIA"
                     Statement = sprintf "integer literal %A lies within its analysed range [%A, %A]" value lower upper
                     Source = fmtRange site.Range; Refs = []
                     Body = ObligationBody.IntegerLiteralRange(value, lower, upper) }
    { NewNodes = [node]; NewEdges = [constrains [site.Id] node]; Annotated = [] }

/// Cross-apply the selected representation's declaration to the actual range.
let integerCoverage (enrichId: int) (name: string) (site: SemanticNode) (lower: bigint) (upper: bigint)
                    (declared: DeclaredRepresentation) (minimum: bigint) (maximum: bigint) : Enrichment =
    let representation = declared.Representation
    let node = obligationNode site enrichId
                   { Id = name; Kind = "integer-representation-coverage"; Logic = "QF_LIA"
                     Statement = sprintf "analysed integer range [%A, %A] fits the declared bounds of selected representation %s (%d bits)" lower upper representation.Name representation.Bits
                     Source = fmtRange site.Range; Refs = []
                     Body = ObligationBody.IntegerRepresentationCoverage(lower, upper, minimum, maximum) }
    { NewNodes = [node]; NewEdges = [constrains [site.Id; declared.Node] node]; Annotated = [] }

/// Compatibility at an ordinary application, separately from laws proved in
/// the callee body. The occurrence carries its instantiated signature; the
/// definition, when resolved, supplies an explicit provenance edge.
let application (enrichId: int) (name: string, (site: SemanticNode, callee: SemanticNode, arguments: SemanticNode list, definition: NodeId option, comparisons: (string * Dimension option * Dimension option) list)) : Enrichment =
    let calleeName = match callee.Kind with SemanticKind.VarRef(name, _) -> name | _ -> "function value"
    let describe = function Some dim -> "<" + Dimension.render dim + ">" | None -> "missing dimensional position"
    let positions = comparisons |> List.map (fun (path, expected, actual) ->
        sprintf "%s: expected %s, actual %s" path (describe expected) (describe actual))
    let node =
        obligationNode site enrichId
            { Id = name; Kind = "dimension-application"; Logic = "QF_LIA"
              Statement = sprintf "dimensional compatibility of this call to %s: %s" calleeName (String.concat "; " positions)
              Source = fmtRange site.Range; Refs = []
              Body = ObligationBody.ApplicationDimensions comparisons }
    { NewNodes = [ node ]
      NewEdges = [ constrains (site.Id :: callee.Id :: (arguments |> List.map (fun argument -> argument.Id)) @ Option.toList definition |> List.distinct) node ]
      Annotated = [] }

/// A source decimal seeds an exact singleton range. Its hosted approximation
/// stays separate; it is never used to reconstruct the source value.
let realLiteral (enrichId: int) (name: string, (site: SemanticNode, source: string, value: ExactRational)) : Enrichment =
    let node = obligationNode site enrichId
                   { Id = name; Kind = "real-literal-range"; Logic = "QF_LRA"
                     Statement = sprintf "source real literal %s has exact singleton range [%s, %s]" source source source
                     Source = fmtRange site.Range; Refs = []
                     Body = ObligationBody.RealLiteralRange(value, value, value) }
    { NewNodes = [node]; NewEdges = [constrains [site.Id] node]; Annotated = [] }

/// Cross-apply the exact source point with the declaration of the current
/// concrete literal representation. The declaration supplies capacity, not
/// evidence about the value, and this claim supplies no rounding guarantee.
let realCoverage (enrichId: int) (site: SemanticNode) (name: string) (source: string) (value: ExactRational)
                 (declared: DeclaredRepresentation) (minimum: ExactRational) (maximum: ExactRational) : Enrichment =
    let representation = declared.Representation
    let node = obligationNode site enrichId
                   { Id = name; Kind = "real-representation-coverage"; Logic = "QF_LRA"
                     Statement = sprintf "source real literal %s lies within the declared finite bounds of %s (%d bits)" source representation.Name representation.Bits
                     Source = fmtRange site.Range; Refs = []
                     Body = ObligationBody.RealRepresentationCoverage(value, value, minimum, maximum) }
    { NewNodes = [node]; NewEdges = [constrains [site.Id; declared.Node] node]; Annotated = [] }

/// A measured operation constrains its two actual operands and result. The
/// rule stays separate from the inferred vectors so discharge checks the
/// operation's relation rather than repeating a precomputed equality.
let dimensional (enrichId: int) (name: string, (site: SemanticNode, left: SemanticNode, right: SemanticNode, rule: DimensionalRule, leftDim: Dimension, rightDim: Dimension, resultDim: Dimension option)) : Enrichment =
    let kind, relation =
        match rule with
        | DimensionalRule.Product -> "product", "(multiplication) adds operand exponents"
        | DimensionalRule.Quotient -> "quotient", "(division) subtracts right operand exponents from left operand exponents"
        | DimensionalRule.SameDimension -> "equality", "preserves the common operand dimension"
        | DimensionalRule.Comparison -> "comparison", "requires equal operand dimensions"
    let resultText = resultDim |> Option.map (fun d -> sprintf ", result <%s>" (Dimension.render d)) |> Option.defaultValue ""
    let node =
        obligationNode site enrichId
            { Id = name; Kind = "dimension-" + kind; Logic = "QF_LIA"
              Statement = sprintf "dimensional %s %s: left <%s>, right <%s>%s" kind relation (Dimension.render leftDim) (Dimension.render rightDim) resultText
              Source = fmtRange site.Range; Refs = []
              Body = ObligationBody.DimensionalRelation (rule, leftDim, rightDim, resultDim) }
    { NewNodes = [ node ]
      NewEdges = [ constrains [ site.Id; left.Id; right.Id ] node ]
      Annotated = [] }

/// storage-reservation, view-containment, terminator-sentinel: one triple per
/// literal, S_f = {literal}. Where `rodata` is declared the literal also
/// carries a residence edge from the declaration.
let literal (rodata: DeclaredSpace option) (enrichId: int) (name: string, (content: string, subject: SemanticNode)) : Enrichment =
    let len = byteLength content
    let storage = len + 1
    let born = fmtRange subject.Range
    let mk = obligationNode subject enrichId
    let storageN =
        mk { Id = sprintf "storage_%s" name; Kind = "storage-reservation"; Logic = "QF_LIA"
             Statement = sprintf "storage for %s is exactly its logical length %d plus one terminator byte (%d = %d + 1)" (describe content) len storage len
             Source = born; Refs = [ "CWE-131" ]; Body = ObligationBody.StorageReservation (len, storage) }
    let viewN =
        mk { Id = sprintf "view_%s" name; Kind = "view-containment"; Logic = "QF_LIA"
             Statement = sprintf "the view handed to write() for %s is exactly %d bytes and strictly inside its %d-byte storage (the terminator is never written)" (describe content) len storage
             Source = born; Refs = [ "CWE-787" ]; Body = ObligationBody.ViewContainment (len, len, storage) }
    let sentinelN =
        mk { Id = sprintf "sentinel_%s" name; Kind = "terminator-sentinel"; Logic = "QF_BV"
             Statement = sprintf "the final storage byte of %s is the 0x00 terminator" (describe content)
             Source = born; Refs = [ "CWE-170" ]; Body = ObligationBody.NulSentinel 0 }
    { NewNodes = [ storageN; viewN; sentinelN ]
      NewEdges =
        (rodata |> Option.map (fun r -> resides r.Node subject.Id) |> Option.toList)
        @ [ constrains [ subject.Id ] storageN
            constrains [ subject.Id ] viewN
            constrains [ subject.Id ] sentinelN ]
      Annotated = [] }

/// Check the actual BAREWire pool that emission consumes. No placement premise
/// is invented: the concrete offsets, extents and declared bounds are evidence.
let staticStorageLayout (enrichId: int) (entry: SemanticNode option) (subject: SemanticNode) (pool: StaticStringPool) : Enrichment =
    let subject = entry |> Option.defaultValue subject
    let slots = pool.Entries |> List.map (fun item -> item.Offset, item.StorageLength, 1)
    let node =
        obligationNode subject enrichId
            { Id = "layout_user_strings"; Kind = "static-storage-layout"; Logic = "QF_LIA"
              Statement = sprintf "BAREWire static string pool: %d settled storages occupy disjoint aligned ranges using %d bytes in the emitted %d-byte allocation (alignment %d, granularity %d), within declared %s capacity %d"
                                  slots.Length pool.UsedSize pool.Size pool.Alignment pool.Granularity pool.SpaceName pool.Capacity
              Source = fmtRange subject.Range; Refs = ["CWE-787"; "CWE-125"; "CWE-131"]
              Body = ObligationBody.StaticStorageLayout(slots, pool.UsedSize, pool.Size, pool.Alignment, pool.Capacity, pool.SpaceAlignment, pool.Granularity) }
    let sources = (entry |> Option.map (fun n -> n.Id) |> Option.toList) @ [pool.DeclarationNode] @ (pool.Entries |> List.collect (fun item -> item.NodeIds))
    { NewNodes = [node]; NewEdges = [constrains (List.distinct sources) node]; Annotated = [] }

/// concat-copy-bound for one String.concat2 site, S_f = {site; left; right}.
/// Operand lengths are pinned where the operand is a literal; the window shape
/// is the emission contract, stated as a theorem over every run.
let concat (enrichId: int) (name: string, (site: SemanticNode, leftId: NodeId, rightId: NodeId, left: (int * string) option, right: (int * string) option)) : Enrichment =
    let pin tag = function
        | Some (len, c) -> sprintf ", with %s = %d (%s)" tag len (describe c)
        | None -> ""
    let node =
        obligationNode site enrichId
            { Id = name; Kind = "concat-copy-bound"; Logic = "QF_LIA"
              Statement = sprintf "for ANY operand lengths a, b >= 0%s%s, the two copy windows of this concatenation ([0,a) then [a,a+b)) lie within its (a+b)-byte allocation: a symbolic theorem over all runs, not a constant check" (pin "a" left) (pin "b" right)
              Source = fmtRange site.Range; Refs = [ "CWE-787"; "CWE-131" ]
              Body = ObligationBody.ConcatCopyBound (left |> Option.map fst, right |> Option.map fst) }
    { NewNodes = [ node ]; NewEdges = [ constrains [ site.Id; leftId; rightId ] node ]; Annotated = [] }

/// The readln site cross-applied with the `consoleReadln` declaration. The
/// buffer's capacity obligations -- BAREWire Platform/Obligations.fs's own
/// vocabulary -- stated by the compiler over the program's actual site; and
/// the site annotated with the capacity the lowering reads instead of authoring.
let readln (platform: DeclaredPlatform) (buffer: DeclaredBuffer) (enrichId: int) (site: SemanticNode) : Enrichment =
    let space = spaceNamed buffer.Space platform
    let s = slug buffer.Name
    let cap = buffer.Capacity
    let source = cite platform buffer.Name
    let spaceText, spaceCap, spaceNode =
        match space with
        | Some sp -> sprintf "the capacity %d of its space %s" sp.Capacity sp.Name, sp.Capacity, [ sp.Node ]
        | None -> sprintf "the capacity of its space %s, which is not declared (taken as 0)" buffer.Space, 0L, []
    let mk = obligationNode site enrichId
    let positive =
        mk { Id = sprintf "capacity_positive_%s" s; Kind = "buffer-capacity"; Logic = "QF_LIA"
             Statement = sprintf "buffer %s declares a positive capacity (%d > 0)" buffer.Name cap
             Source = source; Refs = [ "CWE-131"; "CWE-120" ]; Body = ObligationBody.CapacityPositive cap }
    let fits =
        mk { Id = sprintf "capacity_%s" s; Kind = "buffer-capacity"; Logic = "QF_LIA"
             Statement = sprintf "buffer %s declares capacity %d, at most %s" buffer.Name cap spaceText
             Source = source; Refs = [ "CWE-131"; "CWE-120" ]; Body = ObligationBody.CapacityFits (cap, spaceCap) }
    let bound =
        mk { Id = sprintf "input_bound_%s" s; Kind = "input-buffer-bound"; Logic = "QF_LIA"
             Statement = sprintf "the count handed to the reader of %s is its declared capacity (%d), so the reader writes at most the allocation the same declaration sizes (%d)" buffer.Name cap cap
             Source = source; Refs = [ "CWE-120" ]; Body = ObligationBody.InputBufferBound (cap, cap) }
    let copy =
        if buffer.TrimDelimiter then
            [ mk { Id = sprintf "input_copy_bound_%s" s; Kind = "input-copy-bound"; Logic = "QF_LIA"
                   Statement = sprintf "for any successful read of r bytes into %s (1 <= r <= %d), the trimmed copy of r - 1 bytes is within %d bytes" buffer.Name cap (cap - 1L)
                   Source = source; Refs = [ "CWE-120"; "CWE-787" ]; Body = ObligationBody.InputCopyBound (cap, cap - 1L) } ]
        else []
    { NewNodes = [ positive; fits; bound ] @ copy
      NewEdges =
        [ resides buffer.Node site.Id
          constrains (buffer.Node :: spaceNode) positive
          constrains (buffer.Node :: spaceNode) fits
          constrains [ site.Id; buffer.Node ] bound ]
        @ (copy |> List.map (constrains [ site.Id; buffer.Node ]))
      Annotated = [ annotateBuffer cap source buffer.TrimDelimiter site ] }
