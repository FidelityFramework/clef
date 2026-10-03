# Closed native callback adapters

Status: source specialization of closed handlers is implemented; native boundary acceptance remains blocked as of October 3, 2026. `BAREWire.Descriptors.CallbackDescriptor` declares the native contract. It does not itself establish a complete callable ABI or foreign resource lifetime. The intended application surface accepts an ordinary Clef module function, with adaptation and resource obligations settled by CCS/Baker before native emission.

## Declaration and source contract

`ClosedCallbackDescriptor` has four literal string fields:

| Field | Meaning |
|---|---|
| `Binding` | Fully qualified factory binding, taking one ordinary function and returning a listener record |
| `Adapter` | Fully qualified binding-owned module function, taking that handler first, followed by every native callback parameter |
| `Record` | The listener record named by its existing `CallbackDescriptor` |
| `Field` | Its sole typed `FnPtr` field |

The descriptor, factory and adapter are module declarations. Factory and adapter are immutable named functions without captures. The listener must have exactly one field; its complete entry type must equal the adapter's type after removing the first handler parameter. A matching module-level `CallbackDescriptor` remains mandatory for the declared argument representations, calling convention and return convention. These declaration checks do not discharge the physical ABI or lifetime obligations. A local lookalike descriptor cannot supply the declaration.

The source specialization recognizes this declaration shape (native descriptors omitted here). This illustrates its rewrite contract; it is not a currently admitted foreign payload adapter:

```fsharp
let private adapt handler instance payload data =
    let bytes, count = copyPayloadAndReleaseNativeText payload
    handler bytes count

let private makeEntry (handler: int array -> int -> unit) : MessageListener =
    NativeDefault.zeroed ()

let private closedEntry: Expr<ClosedCallbackDescriptor> = <@ {
    Binding = "Example.Messages.makeEntry"
    Adapter = "Example.Messages.adapt"
    Record = "MessageListener"
    Field = "Invoke" } @>

let inline onMessage source handler =
    connectNative source (makeEntry handler).Invoke
```

The factory body must be exactly `NativeDefault.zeroed ()`, allowing type annotations. The compiler rejects effectful or alternative bodies, and replaces the placeholder's reachable applications before executable elaboration. The application passes a known immutable module function through the inline wrapper. The binding owns copying, release, userdata and native listener declarations.

## Compiler behavior

After type substitution and monomorphization, `Nanopass/ClosedCallbacks.fs` resolves the declaration and the application handler by graph identity. It clones the adapter using the existing subtree cloning machinery, substitutes the handler's module binding, removes the handler formal and creates one ordinary module entry per factory/handler pair. The call becomes a normal listener record containing `FnPtr.ofFunction` of that entry. Native emission additionally requires Baker to settle the complete entry ABI, argument/result adaptations and proof participants, and publish them through Fidelity.PSG. Alex currently refuses a native address or invocation without that realization; its retired function/index repair casts are not restored. Composer has no callback-library names or special wrapper logic.

Saturated inline expansion checks all supplied operands against the declared function domains, evaluates them once in order into ordinary local bindings, and resolves the expanded body in its definition's lexical scope. This keeps unused effectful arguments, shadowing and binding-owned helper resolution lawful.

`CCS8096` rejects malformed or ambiguous declarations, local or mutable template functions, handlers whose closed module identity cannot be established, and adapters whose nested closures capture the removed handler formal. It does not invent a pointer for an unsupported source function.

## Lifetime boundary

This is static specialization of the existing closed-entry capability (Tier C). No captured environment is allocated or retained. Foreign userdata still requires an admitted identity, registration lifetime and retirement contract. An opaque `CHandle` cannot be read, retyped or converted into a bounded view by the adapter. The illustrative payload-copy/release operation above requires its own source-settled boundary adapter; naming it does not provide one. There is no global callback registry and no interior null callback representation.

General closure callbacks still require a real typed environment, declared lifetime, allocation/retention and release, and the per-native-signature trampoline contract. Those Tier A/B obligations are future work; accepting a closed module handler does not establish them. Payload ownership and capacity remain the binding's responsibility even with a closed handler.

## Evidence

`ClosedCallbackCases.fs` covers closed handler specialization, distinct native entries, captured handler rejection, template mutability, nested formal captures, module-only ABI metadata, scalar mismatch retention, inline domain checks and lexical resolution. The October 3 focused boundary acceptance passed 111 tests. Full CCS acceptance passed 1,662 of 1,723 tests; its 61 failures matched the clean baseline's remaining failures, with no new failures, 40 added tests and five baseline failures repaired.

The current Composer `NativeCallbacks` project passes source checking but refuses native emission because the published target ABI realization is missing. `ListenerEntry` is refused with `CCS8403` where foreign lifetime/pointer adapters are unavailable. No native executable from these current gates ran. Earlier native landing results describe their earlier compiler revisions; they do not establish this checkpoint's acceptance.

Before claiming native callback support, retain the existing `func.constant` symbol, `func.call_indirect`, stock MLIR verification and fresh executable checks. Settle the missing ABI and lifetime contracts in Baker, publish immutable proof support in Fidelity.PSG, and have Alex witness those settled rows without inference or repair casts.
