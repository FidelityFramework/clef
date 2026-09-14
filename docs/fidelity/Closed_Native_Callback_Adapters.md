# Closed native callback adapters

Status: implemented closed-handler subset, September 2026. The native callback ABI remains declared by `BAREWire.Descriptors.CallbackDescriptor`. This mechanism lets a binding hide native instance arguments, user data and ownership work while accepting an ordinary Clef module function from its application.

## Declaration and source contract

`ClosedCallbackDescriptor` has four literal string fields:

| Field | Meaning |
|---|---|
| `Binding` | Fully qualified factory binding, taking one ordinary function and returning a listener record |
| `Adapter` | Fully qualified binding-owned module function, taking that handler first, followed by every native callback parameter |
| `Record` | The listener record named by its existing `CallbackDescriptor` |
| `Field` | Its sole typed `FnPtr` field |

The descriptor, factory and adapter are module declarations. Factory and adapter are immutable named functions without captures. The listener must have exactly one field; its complete entry type must equal the adapter's type after removing the first handler parameter. A matching module-level `CallbackDescriptor` remains mandatory and validates native argument widths, pointer dimensions, calling convention and return convention. A local lookalike descriptor cannot supply it.

A binding can declare this shape (native descriptors omitted here):

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

After type substitution and monomorphization, `Nanopass/ClosedCallbacks.fs` resolves the declaration and the application handler by graph identity. It clones the adapter using the existing subtree cloning machinery, substitutes the handler's module binding, removes the handler formal and creates one ordinary module entry per factory/handler pair. The call becomes a normal listener record containing `FnPtr.ofFunction` of that entry. Existing callback validation, representation selection and native `void` entry emission consume this graph. Composer has no callback-library names or special wrapper logic.

Saturated inline expansion checks all supplied operands against the declared function domains, evaluates them once in order into ordinary local bindings, and resolves the expanded body in its definition's lexical scope. This keeps unused effectful arguments, shadowing and binding-owned helper resolution lawful.

`CCS8096` rejects malformed or ambiguous declarations, local or mutable template functions, handlers whose closed module identity cannot be established, and adapters whose nested closures capture the removed handler formal. It does not invent a pointer for an unsupported source function.

## Lifetime boundary

This is static specialization of the existing closed-entry capability (Tier C). No captured environment is allocated or retained, so there is no environment release operation to invent. Native userdata can remain a binding-owned token whose lifetime follows that binding's registration contract. There is no global callback registry and no interior null callback representation.

General closure callbacks still require a real typed environment, declared lifetime, allocation/retention and release, and the per-native-signature trampoline contract. Those Tier A/B obligations are future work; accepting a closed module handler does not establish them. Payload ownership and capacity remain the binding's responsibility even with a closed handler.

## Evidence

`ClosedCallbackCases.fs` covers closed handler specialization, distinct native entries, captured handler rejection, template mutability, nested formal captures, module-only ABI metadata, scalar mismatch retention, inline domain checks and lexical resolution. The native landing witness additionally passes an integer and non-null userdata from C, reads the token only inside the adapter, and proves unused effectful inline arguments run exactly once before the callback.
