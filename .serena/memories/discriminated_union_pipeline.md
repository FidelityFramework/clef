# Discriminated Union Pipeline

> **Litmus test for Baker → SSA → Alex transform chain.**

## The DU Transform Problem

DUs have type heterogeneity: different cases hold different payload types in the same storage slot.

```fsharp
type Number = IntVal of int | FloatVal of float
```

Storage: `{tag: i8, slot: i64}` - the i64 slot holds BOTH int and float bits.

## Three-Phase Pipeline

### Phase 1: Baker Decomposition (FNCS)

Baker transforms high-level DU operations to primitives:

| Input | Output |
|-------|--------|
| `Match` | `IfThenElse` chain with `DUGetTag` + `DUEliminate` per branch |
| `UnionCase` | `DUConstruct` |

**Key files:** `BakerSaturation.fs`, `MatchRecipes.fs`

Match decomposition creates decision tree:
```
match x with
| IntVal i -> bodyA
| FloatVal f -> bodyB
```
→
```
tag = DUGetTag(x)
if tag == 0 then
  i = DUEliminate(x, "IntVal", 0, int)
  bodyA
else
  f = DUEliminate(x, "FloatVal", 1, float)  
  bodyB
```

### Phase 2: SSA Assignment (PSGElaboration)

SSA counts must be **deterministic from PSG structure**.

For `DUConstruct`, count depends on whether bitcast is needed:

```fsharp
let computeDUConstructSSACost arch graph duType payloadOpt =
    match payloadOpt with
    | None -> 3  // Nullary: undef + tagConst + withTag
    | Some payloadId ->
        let payloadMlirType = mapType payloadNode.Type
        let slotType = getSlotTypeFromDULayout duType
        if slotType = payloadMlirType then 4  // Types match
        else 5  // Need bitcast
```

**Key insight:** Compare MLIR types, not NativeTypes. The slot is always i64; payload may be f64.

### Phase 3: MLIR Witnessing (Alex)

`witnessDUConstruct` checks slot vs payload type:

```fsharp
if slotType = payload.Type then
    // Direct insert (4 SSAs)
    insertvalue result, withTag, payload.SSA, [1]
else
    // Bitcast first (5 SSAs)
    bitcast = llvm.bitcast payload.SSA : f64 -> i64
    insertvalue result, withTag, bitcast, [1]
```

`witnessDUEliminate` is symmetric - extract then bitcast if needed.

## The Invariant

> **SSA count in Phase 2 MUST equal SSA usage in Phase 3.**

If Phase 2 allocates 4 SSAs but Phase 3 needs 5 → index out of range.
If Phase 2 allocates 5 SSAs but Phase 3 uses 4 → orphan SSAs (wasteful but safe).

## Debugging Protocol

When DU compilation fails:

1. Check `05_psg2.json` - are DUConstruct nodes present with correct payloads?
2. Check `06_coeffects.json` - do DUConstruct nodes have SSA assignments?
3. Check SSA count vs witness usage - do they match?
4. If type mismatch error in MLIR - slot type ≠ payload type, need bitcast

## Anti-Pattern

**WRONG:** Adding heuristics or padding to SSA counts
**RIGHT:** Compute exact count from type comparison

The SSA count is a pure function of:
- DU layout (from TypeLayout.Inline)
- Payload type (from payload node in PSG)
- Target architecture (for type mapping)
