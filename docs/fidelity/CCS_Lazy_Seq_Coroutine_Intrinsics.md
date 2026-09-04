# CCS Computation Expression Intrinsics

## Overview

This document specifies the **semantic contracts** for computation expression types in CCS. These are the stable "what" - behavioral guarantees that any implementation must satisfy.


### Feature Dependency Graph

```
                    ┌─────────────────────────────────┐
                    │  7. MailboxProcessor (CAPSTONE) │
                    │     Actor-based concurrency     │
                    └───────────────┬─────────────────┘
                                    │ requires
            ┌───────────────────────┼───────────────────────┐
            │                       │                       │
  ┌─────────▼─────────┐   ┌────────▼────────┐   ┌─────────▼─────────┐
  │  3. Async<'T>     │   │ 5. Threading    │   │ 6. Scoped Regions │
  │  Suspendable comp │   │ OS thread prims │   │ Dynamic memory    │
  └─────────┬─────────┘   └─────────────────┘   └───────────────────┘
            │ requires
  ┌─────────▼─────────┐
  │  Closures, State  │
  │  machines         │
  └─────────┬─────────┘
            │ requires
    ┌───────┼───────┐
    │       │       │
┌───▼───┐ ┌─▼───┐ ┌─▼───────┐
│1.Lazy │ │2.Seq│ │Records, │
│       │ │     │ │DUs, etc │
└───────┘ └─────┘ └─────────┘
```

**MailboxProcessor is the capstone feature** - it builds on async (for the message loop), closures (for behavior functions), threading primitives (for true parallelism), and scoped regions (for dynamic memory within worker threads). It represents the culmination of the WRENStack feature set.

---

## Architectural Principle

```
CCS (This Document)              Alex (Implementation)
─────────────────────             ────────────────────────
Semantic contracts                Strategy: StateMachine
Type signatures                   Strategy: DCont (future)
Behavioral laws                   Strategy: ... (extensible)
Coeffect interactions
```

CCS defines **what** these types mean. Alex provides **how** to compile them. This separation allows implementation strategies to evolve without changing the language semantics.

---

## 1. Lazy<'T> - Deferred Computation

### Type

```fsharp
type Lazy<'T>
```

A computation of type `'T` that is evaluated at most once, on demand.

### Operations

| Operation | Type | Description |
|-----------|------|-------------|
| `Lazy.create` | `(unit -> 'T) -> Lazy<'T>` | Wrap a thunk |
| `Lazy.force` | `Lazy<'T> -> 'T` | Evaluate and return result |
| `Lazy.isValueCreated` | `Lazy<'T> -> bool` | Check if already evaluated |

### Semantic Laws

1. **Idempotence**: `force (force lazy) ≡ force lazy`
2. **At-most-once**: The wrapped thunk executes at most once
3. **Memoization**: After first `force`, subsequent calls return cached value
4. **Purity preservation**: If thunk is pure, result is deterministic

### Coeffect Interaction

| Thunk Coeffect | Lazy Behavior |
|----------------|---------------|
| Pure | Safe to memoize, can be shared |
| IO | Memoization captures effect timing |
| Mutable | First force captures mutation state |

### NTUKind

`NTUlazy` - New discriminated union case in NativeTypes.

---

## 2. Seq<'T> - Lazy Iteration

### Type

```fsharp
type Seq<'T>
```

A lazy, pull-based sequence of values of type `'T`.

### Operations

| Operation | Type | Description |
|-----------|------|-------------|
| `Seq.empty` | `Seq<'T>` | Empty sequence |
| `Seq.singleton` | `'T -> Seq<'T>` | Single element |
| `Seq.map` | `('T -> 'U) -> Seq<'T> -> Seq<'U>` | Transform elements |
| `Seq.filter` | `('T -> bool) -> Seq<'T> -> Seq<'T>` | Filter elements |
| `Seq.collect` | `('T -> Seq<'U>) -> Seq<'T> -> Seq<'U>` | Flat map |
| `Seq.fold` | `('S -> 'T -> 'S) -> 'S -> Seq<'T> -> 'S` | Left fold |
| `Seq.take` | `int -> Seq<'T> -> Seq<'T>` | Take first N |
| `Seq.skip` | `int -> Seq<'T> -> Seq<'T>` | Skip first N |
| `Seq.iter` | `('T -> unit) -> Seq<'T> -> unit` | Side-effecting iteration |
| `Seq.toArray` | `Seq<'T> -> 'T[]` | Materialize |
| `Seq.toList` | `Seq<'T> -> 'T list` | Materialize |

### Semantic Laws

1. **Laziness**: Elements computed on demand, not eagerly
2. **Pull-based**: Consumer controls iteration pace
3. **Composability**: Operations compose without intermediate materialization
4. **Restartability**: Iterating a seq twice re-executes the computation

### Iteration Protocol (Abstract)

A `Seq<'T>` supports iteration via an abstract protocol:
- **Advance**: Move to next element (may produce or exhaust)
- **Current**: Access current element (valid after successful advance)
- **Reset**: Restart iteration from beginning

The concrete representation of this protocol is strategy-dependent.

### Coeffect Interaction

| Body Coeffect | Seq Behavior |
|---------------|--------------|
| Pure | Can be iterated multiple times identically |
| IO | Each iteration re-executes effects |
| Mutable | Each iteration sees current state |

### `seq { }` Builder

The computation expression:
```fsharp
seq {
    yield x
    yield! xs
    for i in source do yield f(i)
}
```

Desugars to Seq operations. Implementation strategy determines compilation.

---

## 3. Async<'T> - Suspendable Computation

### Type

```fsharp
type Async<'T>
```

A computation of type `'T` that may suspend and resume.

### Operations

| Operation | Type | Description |
|-----------|------|-------------|
| `Async.Return` | `'T -> Async<'T>` | Lift pure value |
| `Async.Bind` | `Async<'T> -> ('T -> Async<'U>) -> Async<'U>` | Sequence computations |
| `Async.Zero` | `Async<unit>` | Empty async |
| `Async.Combine` | `Async<unit> -> Async<'T> -> Async<'T>` | Sequential composition |
| `Async.Delay` | `(unit -> Async<'T>) -> Async<'T>` | Delay evaluation |
| `Async.Start` | `Async<unit> -> unit` | Fire and forget |
| `Async.StartChild` | `Async<'T> -> Async<Async<'T>>` | Fork computation |
| `Async.RunSynchronously` | `Async<'T> -> 'T` | Block until complete |
| `Async.Parallel` | `Async<'T>[] -> Async<'T[]>` | Concurrent execution |
| `Async.Sleep` | `int -> Async<unit>` | Delay (milliseconds) |

### Semantic Laws

1. **Monad laws**: Return/Bind satisfy left identity, right identity, associativity
2. **Suspension**: `Bind` marks potential suspension points
3. **Resumption**: Suspended computation can be resumed
4. **Composition**: Asyncs compose via Bind without blocking

### `async { }` Builder

The computation expression:
```fsharp
async {
    let! x = fetchAsync()
    let! y = processAsync(x)
    return combine(x, y)
}
```

Desugars to Async.Bind chains. Implementation strategy determines suspension mechanism.

### Coeffect Interaction

| Operation | Coeffects |
|-----------|-----------|
| `let!` | Suspension point, IO |
| `do!` | Suspension point, IO |
| `return` | Pure |
| `Async.Start` | Concurrent |

---

## 4. MailboxProcessor<'Msg> - Actor-Based Concurrency (CAPSTONE)

### Type

```fsharp
type MailboxProcessor<'Msg>
type AsyncReplyChannel<'Reply>
```

An actor that processes messages of type `'Msg` sequentially on a dedicated execution context, with optional request-reply patterns.

**This is the capstone feature** of the WRENStack computation model, building on:
- `Async<'T>` for the message processing loop
- Closures for behavior functions
- Threading primitives for true parallelism

### Operations

| Operation | Type | Description |
|-----------|------|-------------|
| `MailboxProcessor.Start` | `(MailboxProcessor<'Msg> -> Async<unit>) -> MailboxProcessor<'Msg>` | Create and start actor |
| `MailboxProcessor.Post` | `'Msg -> unit` | Send message (fire-and-forget) |
| `MailboxProcessor.PostAndReply` | `(AsyncReplyChannel<'Reply> -> 'Msg) -> 'Reply` | Send and wait for reply |
| `MailboxProcessor.PostAndAsyncReply` | `(AsyncReplyChannel<'Reply> -> 'Msg) -> Async<'Reply>` | Send and async wait |
| `MailboxProcessor.TryPostAndReply` | `(AsyncReplyChannel<'Reply> -> 'Msg) -> int -> 'Reply option` | With timeout |
| `MailboxProcessor.Receive` | `unit -> Async<'Msg>` | Receive next message |
| `MailboxProcessor.TryReceive` | `int -> Async<'Msg option>` | Receive with timeout |
| `MailboxProcessor.Scan` | `('Msg -> Async<'T> option) -> Async<'T>` | Selective receive |
| `MailboxProcessor.CurrentQueueLength` | `int` | Messages waiting |

### Semantic Laws

1. **Sequential Processing**: Messages processed one at a time in FIFO order
2. **Isolation**: Actor state is encapsulated; only accessible within the behavior function
3. **Non-blocking Send**: `Post` returns immediately; does not wait for processing
4. **Blocking Receive**: `Receive` suspends until a message is available
5. **Reply Correlation**: `PostAndReply` correlates request with specific response

### Message Ordering Guarantees

| Scenario | Guarantee |
|----------|-----------|
| Single sender | Messages arrive in send order |
| Multiple senders | Per-sender ordering preserved; interleaving unspecified |
| Reply channels | Reply delivered to correct waiter |

### Actor Lifecycle

```
Created ──Start()──► Running ──────► Processing
                        │                │
                        │    ◄───────────┘
                        │      (loop continues)
                        │
                        └──(exception/dispose)──► Stopped
```

### Coeffect Interaction

| Operation | Coeffects |
|-----------|-----------|
| `Start` | Spawns execution context (Thread coeffect) |
| `Post` | Non-blocking send (minimal) |
| `PostAndReply` | Blocking wait (Suspension) |
| `Receive` | Suspension point |
| Behavior body | Inherits async coeffects |

### Canonical Usage Pattern

```fsharp
type Message =
    | Compute of data: int * AsyncReplyChannel<int>
    | Shutdown

let worker = MailboxProcessor.Start(fun inbox ->
    let rec loop state = async {
        let! msg = inbox.Receive()
        match msg with
        | Compute (data, reply) ->
            let result = expensiveComputation data
            reply.Reply(result)
            return! loop state
        | Shutdown ->
            return ()  // Exit loop, actor stops
    }
    loop initialState
)

// Usage from another context
let! result = worker.PostAndAsyncReply(fun reply -> Compute(42, reply))
```

### NTUKind

`NTUmailbox` - Discriminated union case for MailboxProcessor representation.
`NTUreplyChannel` - Discriminated union case for AsyncReplyChannel.

---

## 5. Threading Primitives

These low-level intrinsics support MailboxProcessor and explicit threading scenarios.

### Thread Operations

| Operation | Type | Description |
|-----------|------|-------------|
| `Thread.create` | `(unit -> unit) -> ThreadHandle` | Spawn OS thread |
| `Thread.join` | `ThreadHandle -> unit` | Wait for completion |
| `Thread.sleep` | `int -> unit` | Sleep milliseconds |
| `Thread.yield` | `unit -> unit` | Yield to scheduler |
| `Thread.currentId` | `unit -> int` | Current thread ID |

### Synchronization Primitives

| Operation | Type | Description |
|-----------|------|-------------|
| `Mutex.create` | `unit -> Mutex` | Create mutex |
| `Mutex.lock` | `Mutex -> unit` | Acquire (blocking) |
| `Mutex.tryLock` | `Mutex -> bool` | Try acquire (non-blocking) |
| `Mutex.unlock` | `Mutex -> unit` | Release |
| `Mutex.dispose` | `Mutex -> unit` | Destroy |

### Condition Variables

| Operation | Type | Description |
|-----------|------|-------------|
| `CondVar.create` | `unit -> CondVar` | Create condition variable |
| `CondVar.wait` | `CondVar -> Mutex -> unit` | Wait (releases mutex) |
| `CondVar.waitTimeout` | `CondVar -> Mutex -> int -> bool` | Wait with timeout |
| `CondVar.signal` | `CondVar -> unit` | Wake one waiter |
| `CondVar.broadcast` | `CondVar -> unit` | Wake all waiters |

### Atomic Operations

| Operation | Type | Description |
|-----------|------|-------------|
| `Atomic.load` | `Ptr<'T, 'Region, ReadWrite> -> 'T` | Atomic read |
| `Atomic.store` | `Ptr<'T, 'Region, ReadWrite> -> 'T -> unit` | Atomic write |
| `Atomic.compareExchange` | `Ptr<'T, 'Region, ReadWrite> -> 'T -> 'T -> 'T` | CAS, returns old |
| `Atomic.fetchAdd` | `Ptr<int, 'Region, ReadWrite> -> int -> int` | Add, returns old |
| `Atomic.fetchSub` | `Ptr<int, 'Region, ReadWrite> -> int -> int` | Subtract, returns old |

### Memory Ordering

| Ordering | Description |
|----------|-------------|
| `Relaxed` | No ordering guarantees |
| `Acquire` | Reads after this see writes before Release |
| `Release` | Writes before this visible after Acquire |
| `SeqCst` | Total ordering (strongest) |

Default is `SeqCst` for safety. Relaxed orderings available via explicit annotation.

### Semantic Laws

1. **Thread Independence**: Spawned threads have independent execution
2. **Mutex Exclusion**: At most one thread holds a locked mutex
3. **CondVar Atomicity**: Wait atomically releases mutex and sleeps
4. **Atomic Visibility**: Atomic operations have specified memory ordering

### Coeffect Interaction

| Operation | Coeffects |
|-----------|-----------|
| `Thread.create` | Concurrent (spawns parallel execution) |
| `Thread.join` | Suspension (blocks until completion) |
| `Mutex.lock` | Suspension (may block) |
| `CondVar.wait` | Suspension (always blocks) |
| `Atomic.*` | Minimal (single instruction) |

### NTUKind

`NTUthread` - Thread handle representation.
`NTUmutex` - Mutex representation.
`NTUcondvar` - Condition variable representation.

---

## 6. Region - Scoped Dynamic Memory

### Type

```fsharp
type Region
```

A **linear resource type** representing a scoped memory region with bump-pointer allocation and bulk deallocation. The compiler tracks Region lifetime and infers disposal points - no interface required.

### Design Principles

1. **Compiler-inferred disposal**: No `IDisposable`, no `use` keyword required. The compiler knows `Region` needs cleanup and inserts disposal at scope exits.

2. **Linear resource**: Each `Region` is consumed exactly once. Compiler error if not disposed or if used after disposal.

3. **Scope-bound lifetime**: Disposal is determined by lexical scope, not reachability. Deterministic, no tracing.

4. **No escape**: Data allocated in a region cannot outlive the region without explicit copy.

### Operations

| Operation | Type | Description |
|-----------|------|-------------|
| `Region.create` | `int -> Region` | Create growable region with initial pages |
| `Region.createFixed` | `int -> Region` | Create non-growable region (embedded targets) |
| `Region.alloc<'T>` | `Region -> int -> 'T[]` | Bump-allocate array |
| `Region.allocSingle<'T>` | `Region -> 'T` | Allocate single value |
| `Region.grow` | `Region -> int -> unit` | Add pages (explicit, growable only) |
| `Region.release` | `Region -> unit` | Early release (compiler usually infers) |
| `Region.usedBytes` | `Region -> int` | Diagnostic: bytes allocated |
| `Region.committedBytes` | `Region -> int` | Diagnostic: pages committed |
| `Region.copyOut<'T>` | `'T[] -> 'T[]` | Copy to caller's context (escape hatch) |

### Compiler-Inferred Disposal

The compiler performs scope analysis and inserts `Region.release` at all exit points:

```fsharp
// What you write
let processData input =
    let region = Region.create 4
    let buffer = Region.alloc<byte> region 1024
    transform buffer

// What compiler generates
let processData input =
    let region = Region.create 4
    let buffer = Region.alloc<byte> region 1024
    let __result = transform buffer
    Region.release region  // <-- Compiler inserted
    __result
```

Multiple exit points are handled automatically:

```fsharp
let compute x =
    let region = Region.create 2
    if x < 0 then
        -1                    // Compiler inserts: Region.release region
    elif x = 0 then
        0                     // Compiler inserts: Region.release region
    else
        let result = work region x
        result                // Compiler inserts: Region.release region
```

### Region Parameter Passing

Regions can be passed to functions. The caller's scope determines lifetime:

```fsharp
let helper (r: Region) (data: byte[]) =
    let temp = Region.alloc<int> r 100  // Allocates in caller's region
    process temp data

let main () =
    let region = Region.create 4
    let input = Region.alloc<byte> region 1024
    helper region input  // helper uses same region
    // Compiler inserts: Region.release region
```

### Nested Regions

Regions can nest. Disposal order is reverse of creation:

```fsharp
let nested () =
    let outer = Region.create 4
    let inner = Region.create 2
    // ... work ...
    // Compiler inserts (reverse order):
    // Region.release inner
    // Region.release outer
```

### Escape Prevention

Data allocated in a region cannot escape without explicit copy:

```fsharp
let bad () =
    let region = Region.create 2
    let data = Region.alloc<int> region 10
    data  // Compiler ERROR: 'data' would escape region lifetime

let good () =
    let region = Region.create 2
    let data = Region.alloc<int> region 10
    Region.copyOut data  // OK: explicitly copied to caller's context
```

### Semantic Laws

1. **Linearity**: Each `Region` consumed exactly once
2. **Scope-bound**: Disposal at scope exit, not reachability
3. **Bulk release**: All allocations freed together (no individual free)
4. **No escape**: Region-allocated data cannot outlive region without copy
5. **Deterministic**: Disposal point known at compile time
6. **Growable default**: `create` allows growth; `createFixed` for constrained targets

### Coeffect Interaction

| Operation | Coeffects |
|-----------|-----------|
| `Region.create` | Allocates pages (Resource acquisition) |
| `Region.alloc` | Pure within region (bump pointer) |
| `Region.grow` | May syscall (IO) |
| `Region.release` | Frees pages (Resource release) |

Functions using regions are tracked:

```fsharp
let parse (r: Region) (input: string) : ParseTree =  // Coeffect: uses Region r
    let nodes = Region.alloc<Node> r 100
    // ...
```

### Use with MailboxProcessor

Scoped regions provide dynamic memory for actor worker threads:

```fsharp
let worker = MailboxProcessor.Start(fun inbox ->
    async {
        while true do
            let! (data, reply) = inbox.Receive()

            // Region for this message's computation
            let region = Region.create 8
            let intermediate = Region.alloc<float> region 10000
            let result = heavyComputation region intermediate data
            let output = Region.copyOut result
            // Region.release region (compiler-inserted)

            reply.Reply(output)
    }
)
```

### NTUKind

`NTUregion` - Region handle representation.

### What This Is NOT

| Not This | Because |
|----------|---------|
| IDisposable pattern | No interface, compiler-intrinsic type |
| Manual dispose calls | Compiler infers disposal points |
| GC finalizers | No GC, deterministic scope exit |
| Reference counting | No counting, bulk release |
| Full borrow checker | Simpler - just escape analysis |
| Olivier arena | No actor coupling, no sentinels |

---

## 8. Coeffect System Integration

These types interact with CCS coeffect tracking:

| Type | Primary Coeffects |
|------|-------------------|
| `Lazy<'T>` | Captures thunk coeffects, memoization semantics |
| `Seq<'T>` | Per-element coeffects, iteration timing |
| `Async<'T>` | IO, Suspension, potentially Concurrent |
| `Region` | Resource acquisition/release, scope-bound |
| `MailboxProcessor<'Msg>` | Concurrent (spawns thread), Suspension (receive) |
| `Thread/Mutex/CondVar` | Concurrent, Suspension |
| `Atomic.*` | Minimal (single-instruction side effects) |

Coeffect analysis determines:
- Whether lazy values can be safely shared
- Whether seq iterations have observable effects
- Whether async computations need synchronization
- **Whether region-allocated data escapes its scope**
- **Whether actor message handlers are safe to execute concurrently**
- **Whether threading primitives require memory barriers**

### Thread Safety Analysis

The coeffect system tracks thread-related effects:

| Coeffect | Meaning |
|----------|---------|
| `Pure` | No threading concerns, freely shareable |
| `Concurrent` | Spawns or interacts with other threads |
| `Suspension` | May block current thread |
| `Mutable` | Accesses mutable state (requires synchronization if Concurrent) |

A function marked `Concurrent + Mutable` requires explicit synchronization (mutex, atomic, or actor isolation).

---

## 9. What This Document Does NOT Specify

The following are **implementation concerns**, not semantic contracts:

- Memory layout of types (struct fields, sizes)
- State machine encoding for seq/async
- LLVM/MLIR emission patterns
- Coroutine frame structure
- MoveNext function signatures
- **Message queue implementation (lock-free vs mutex)**
- **Thread pool vs dedicated thread strategy**
- **Platform-specific thread APIs (pthread vs Win32)**
- **Actor supervision and restart policies** (Olivier/Prospero concern)

These belong in Alex implementation strategy documentation.

---

## 10. Implementation Strategy Overview

While CCS defines semantics, Alex provides multiple implementation strategies:

| Feature | Foundational Strategy | Future Strategy |
|---------|----------------------|-----------------|
| `Lazy<'T>` | Struct with flag + value | (stable) |
| `Seq<'T>` | MoveNext state machine (LLVM coro) | DCont generators |
| `Async<'T>` | State machine (LLVM coro) | DCont |
| `Region` | OS pages (mmap/VirtualAlloc) | Page pool, static arena |
| `MailboxProcessor` | OS thread + mutex queue (LLVM coro for loop) | Olivier (arena per actor) |
| Threading | Direct syscalls (pthread/Win32) | RTOS mapping (embedded) |

**Foundational Strategy** uses only upstream MLIR dialects and LLVM intrinsics.
This is the production target for embedded/MCU/unikernel deployments.

**Future Strategies** may use custom dialects (DCont, Inet) or platform-specific optimizations.


---

## Related Documentation

**Semantic (CCS)**:
- `clef-lang-spec/spec/lazy-representation.md`, `seq-representation.md`, `seq-operations-representation.md`
- `/home/hhh/repos/clef/.serena/memories/coeffect_compilation_strategy.md`

**Implementation (Alex)**:

**WRENStack**:
- `Composer/docs/WRENStack_Roadmap.md`
- `Composer/docs/FidelityHelloWorld_Progression.md`
