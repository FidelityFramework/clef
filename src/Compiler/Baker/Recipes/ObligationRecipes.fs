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
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution
open Clef.Compiler.Baker.Ingredients.Obligations

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

/// memory-map-disjointness over all reachable literals: consecutive placement
/// from a symbolic base, pairwise disjoint, exact span -- and, where `rodata`
/// is declared, the span within its capacity. Arity |L| + 1: a clique of
/// pairwise claims does not entail the span.
let layout (platform: DeclaredPlatform option) (rodata: DeclaredSpace option) (enrichId: int) (literals: (string * SemanticNode) list) : Enrichment =
    match literals with
    | [] | [ _ ] -> Enrichment.empty
    | (_, subject) :: _ ->
        let storages = literals |> List.map (fun (c, _) -> byteLength c + 1)
        let span = List.sum storages
        let cited, capacity, source =
            match platform, rodata with
            | Some p, Some r ->
                sprintf ", within the %d-byte capacity of the declared space %s" r.Capacity r.Name, Some r.Capacity, cite p r.Name
            | _ -> "", None, "all reachable string literals, entry unit and platform library"
        let node =
            obligationNode subject enrichId
                { Id = "layout_user_strings"; Kind = "memory-map-disjointness"; Logic = "QF_LIA"
                  Statement = sprintf "the %d reachable string storages, laid out consecutively, occupy pairwise-disjoint ranges spanning exactly %d bytes%s" storages.Length span cited
                  Source = source; Refs = [ "CWE-787"; "CWE-125" ]
                  Body = ObligationBody.ConsecutiveLayout (storages, span, capacity) }
        let sources = (literals |> List.map (fun (_, n) -> n.Id)) @ (rodata |> Option.map (fun r -> r.Node) |> Option.toList)
        { NewNodes = [ node ]; NewEdges = [ constrains sources node ]; Annotated = [] }

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
