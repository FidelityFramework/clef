/// Process ownership for the checker's counters, measure cells and phase settings.
module Clef.Compiler.CheckExecution

open Clef.Compiler.NativeTypedTree.Infrastructure
open System.Threading

let private gate = obj()
let mutable private waiting = 0

/// Internal diagnostic for deterministic ownership tests; includes only calls
/// that have requested entry and have not yet acquired the process gate.
let internal waitingCount () = Volatile.Read(&waiting)

/// Reentrant so a complete project operation may call guarded parser/checker APIs.
let synchronized (work: unit -> 'T) : 'T =
    let mutable entered = false
    Interlocked.Increment(&waiting) |> ignore
    try
        try Monitor.Enter(gate, &entered)
        finally Interlocked.Decrement(&waiting) |> ignore
        work ()
    finally
        if entered then Monitor.Exit gate

/// Configuration belongs to this entire operation, including result projection.
let run (configuration: PhaseConfig.ArtifactConfig) (work: unit -> 'T) : 'T =
    synchronized (fun () ->
        let previous = PhaseConfig.getConfig ()
        try
            PhaseConfig.setConfig configuration
            work ()
        finally
            PhaseConfig.setConfig previous)
