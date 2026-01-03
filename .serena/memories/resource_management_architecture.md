# Fidelity Resource Management Architecture

> **Source**: SpeakEZ blog articles on RAII, delimited continuations, and resource management
> **Created**: January 3, 2026

## Core Principle: IDisposable is NOT an F# Native Concern

In the Fidelity ecosystem, `System.IDisposable` is fundamentally incompatible with the native compilation model. Resource cleanup is handled through:

1. **RAII Principles** - Scope-based lifetimes
2. **Delimited Continuations** - Reset/shift boundaries establish resource scopes
3. **Compile-Time Analysis** - No runtime tracking overhead
4. **Actor Lifetimes** - Automatic cleanup when actors terminate

## Why IDisposable is Wrong for Fidelity

| IDisposable Requirement | Fidelity Incompatibility |
|------------------------|-------------------------|
| Runtime state tracking | Fidelity uses compile-time analysis |
| GC/finalizer integration | Fidelity has no GC |
| Object-oriented disposal | Fidelity is functional (continuations/scopes) |
| BCL dependency | Fidelity is BCL-free |
| Explicit `use` patterns | Fidelity's scope analysis is automatic |

## The RAII Model in Fidelity

From "RAII in Olivier and Prospero":

- **Actor-Scoped Lifetimes**: Each actor owns an arena that lives exactly as long as the actor
- **Deterministic Cleanup**: Resources reclaimed when actors terminate, not through `Dispose()`
- **No Garbage Collection**: Static binding specializes allocation strategies
- **Compile-Time Resource Analysis**: Firefly automatically inserts cleanup during IR lowering

## Delimited Continuations for Resource Scopes

From "Delimited Continuations: Fidelity's Turning Point":

- **Reset/Shift Boundaries**: Establish explicit resource scopes
- **Automatic Cleanup at Boundaries**: Cleanup happens when computation exits a continuation boundary
- **Stack Allocation**: Resources captured across suspension points are stack-allocated
- **Algebraic Effects Model**: Hardware drivers use effect interpreters at system boundaries

## Scope-Based Cleanup vs Runtime Tracking

From "The Continuation Preservation Paradox":

- **Region-Based Allocation**: Captured variables in memory regions with controlled lifetimes
- **Lifetime Tied to Continuation**: Region's lifetime tied to the closure/continuation itself
- **Zero-Runtime Overhead**: No reference counting, no disposal tracking, no finalization queues

## Practical Implications for Alloy

1. **Remove `System.IDisposable` references** - Not just replace, REMOVE entirely
2. **No custom IDisposable interface** - The concept doesn't exist in native F#
3. **Rely on scope analysis** - Firefly compiler determines cleanup from continuation/scope structure
4. **Stack allocation where possible** - Resources in controlled lifetime regions

## Key Quote

> "In our actor system, this means each actor owns an arena that lives exactly as long as the actor does. No scanning, no heuristics, no unpredictability - just deterministic cleanup when actors complete their lifecycle."

## References

- "Delimited Continuations: Fidelity's Turning Point" (Dec 2025)
- "RAII in Olivier and Prospero" (Jun 2023)  
- "The Continuation Preservation Paradox" (Jul 2025)
- `/docs/Architecture_Canonical.md`
