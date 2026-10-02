namespace Clef.Compiler.Project

open System
open System.Threading
open Clef.Compiler.NativeTypedTree.Infrastructure
open Fidelity.FSharp.Incremental
open Fidelity.FSharp.Incremental.Hosting

[<RequireQualifiedAccess>]
type ProjectWorkspaceError =
    | Closed
    | Superseded
    | Released
    | InvalidRevision
    | ConflictingInputs
    | Busy
    | LifetimeLimitReached
    | CheckFailed of string
    | HostFailed of string

module private WorkspaceProtocol =
    let error = function
        | MailboxError.Closed -> ProjectWorkspaceError.Closed
        | MailboxError.QueueFull -> ProjectWorkspaceError.Busy
        | other -> ProjectWorkspaceError.HostFailed(sprintf "%A" other)

    let observe operation = async {
        let! receipt = AsyncMailbox.observe operation
        return receipt |> Result.map ignore |> Result.mapError error
    }

/// Retain this acknowledgement before changing project inputs. Cancelling an
/// observation does not undo reservation; the same receipt can be observed again.
type ProjectReservation internal (revision: int64, operation: AsyncMailbox.Operation) =
    member _.Revision = revision
    member _.ObserveAsync() = async {
        let! result = WorkspaceProtocol.observe operation
        return result |> Result.map (fun () -> revision)
    }

/// One consumer's interest. Observation cancellation never withdraws this handle.
/// ReleaseAsync is repeatable and owns the withdrawal independently of observers.
type ProjectDemand<'View> internal
    (revision: int64, identity: string, observe: unit -> Async<Result<'View, ProjectWorkspaceError>>,
     release: unit -> Async<Result<unit, ProjectWorkspaceError>>) =
    member _.Revision = revision
    member _.Identity = identity
    member _.ObserveAsync() = observe ()
    member _.ReleaseAsync() = release ()

type private ProjectGeneration<'View> = {
    Revision: int64
    Overrides: Map<string, string>
    mutable Prepared: PreparedProject option
    Setup: AsyncMailbox.Operation list
    mutable Output: (ValueToken * Result<'View, ProjectWorkspaceError>) option
}

/// A cold, CCS-owned whole-project coordinator. A generation has one immutable
/// capture, shared checks and consumer demands; a reserved edit never reuses a
/// prior generation's result or proof. Projectors must freeze their public view
/// while the process-wide compiler gate is held. Close and create a new workspace
/// after 4,096 reservations or 65,536 demands; retained protocol identifiers are
/// never recycled within an epoch, and their lifetime storage is therefore bounded.
type ProjectWorkspace<'View> internal
    (projectPath: string, project: ProjectCheckResult -> 'View, configuration: PhaseConfig.ArtifactConfig,
     prepare: string -> Map<string, string> -> Result<PreparedProject, string>) =

    let gate = obj()
    let identity = Guid.NewGuid().ToString("N")
    let capacity = 256
    let mutable revision = 0L
    let mutable nextDemand = 0UL
    // Reserve one command slot for every live consumer's eventual withdrawal.
    // Release admission therefore never needs a cancellable backpressure wait.
    let mutable activeDemands = 0
    let mutable closing = false
    let mutable generation: ProjectGeneration<'View> option = None
    let work value = WorkId(uint64 value)

    let evaluate invocation cancellation = async {
        match invocation with
        | StepInvocation.Resume _ ->
            return StepOutcome.Complete(Completion.Failed { Code = "ccs-resume"; Message = "Whole-project checks do not suspend." })
        | StepInvocation.Start request ->
            let (RevisionId requested) = request.Revision
            let captured = lock gate (fun () ->
                generation |> Option.filter (fun value -> uint64 value.Revision = requested && not closing))
            match captured with
            | None -> return StepOutcome.Complete Completion.Cancelled
            | Some captured ->
                // The synchronous checker cannot be interrupted. Explicit work
                // cancellation revokes eligibility; ownership continues through
                // checking, projection and configuration restoration.
                let result =
                    if WorkCancellation.isRequested cancellation then None
                    else
                        // Capture is owned work too: close joins its synchronous
                        // I/O, while control admission never holds its state gate
                        // across a read. Every semantic input is frozen before
                        // checking; this explicit generation is never hash-reused.
                        let prepared =
                            match lock gate (fun () -> captured.Prepared) with
                            | Some prepared -> Ok prepared
                            | None ->
                                prepare projectPath captured.Overrides
                                |> Result.map (fun prepared ->
                                    // A withdrawn first attempt may still finish
                                    // capture. Keep those immutable bytes for a
                                    // later demand of this same generation.
                                    lock gate (fun () ->
                                        match captured.Prepared with
                                        | Some existing -> existing
                                        | None -> captured.Prepared <- Some prepared; prepared))
                        match prepared with
                        | Error message -> Some(Error(ProjectWorkspaceError.CheckFailed message))
                        | Ok _ when WorkCancellation.isRequested cancellation -> None
                        | Ok prepared ->
                            Clef.Compiler.CheckExecution.run configuration (fun () ->
                                if WorkCancellation.isRequested cancellation then None
                                else
                                    try Some(Ok(project (ProjectChecker.checkPrepared prepared)))
                                    with error -> Some(Error(ProjectWorkspaceError.CheckFailed error.Message)))
                match result with
                | None -> return StepOutcome.Complete Completion.Cancelled
                | Some result ->
                    let (AttemptId attempt) = request.Attempt
                    let value = ValueToken attempt
                    lock gate (fun () -> captured.Output <- Some(value, result))
                    return StepOutcome.Complete(
                        match result with
                        | Ok _ -> Completion.Succeeded value
                        | Error(ProjectWorkspaceError.CheckFailed message) -> Completion.Failed { Code = "ccs-check"; Message = message }
                        | Error error -> Completion.Failed { Code = "ccs-check"; Message = sprintf "%A" error })
    }

    let host =
        AsyncMailbox.create { Epoch = EpochId 1UL; MaxConcurrency = 1; CommandCapacity = capacity } evaluate
        |> Result.defaultWith (fun error -> invalidOp (sprintf "%A" error))

    let admit action = AsyncMailbox.admit action host |> Result.mapError WorkspaceProtocol.error
    let start () = AsyncMailbox.start host |> Result.mapError WorkspaceProtocol.error
    let currentOutput () =
        match generation with
        | Some current when not closing ->
            match AsyncMailbox.tryResult (work current.Revision) host, current.Output with
            | Some handle, Some(token, Ok result) when handle.Value = token && AsyncMailbox.isEligible handle host ->
                Some(current.Revision, result)
            | _ -> None
        | _ -> None

    new(projectPath, project, ?configuration) =
        ProjectWorkspace(projectPath, project, defaultArg configuration PhaseConfig.defaultConfig, ProjectChecker.prepare)

    member _.Revision = lock gate (fun () -> revision)
    member _.Identity = identity
    member _.Current = lock gate currentOutput
    /// Includes failures from withdrawn work; a successful close is a cleanup
    /// receipt and does not erase evaluation diagnostics.
    member _.DrainDiagnostics() = AsyncMailbox.drainDiagnostics host

    /// Immediate admission; never waits for a running checker. Observe the
    /// retained acknowledgement successfully before mutating disk/editor inputs.
    member _.BeginReserve() : Result<ProjectReservation, ProjectWorkspaceError> =
        lock gate (fun () ->
            if closing then Error ProjectWorkspaceError.Closed
            elif revision >= 4096L then Error ProjectWorkspaceError.LifetimeLimitReached
            elif (AsyncMailbox.snapshot host).QueuedCommands + activeDemands >= capacity then Error ProjectWorkspaceError.Busy
            else
                start () |> Result.bind (fun () ->
                    let requested = revision + 1L
                    admit (Action.ReserveScope(ScopeId 1UL, RevisionId(uint64 requested)))
                    |> Result.map (fun operation ->
                        revision <- requested
                        generation <- None
                        ProjectReservation(requested, operation))))

    member this.ReserveAsync() = async {
        match this.BeginReserve() with
        | Error error -> return Error error
        | Ok reservation -> return! reservation.ObserveAsync()
    }

    /// Admits a retained consumer of this immutable revision/override request.
    /// The owned evaluator captures input bytes once before checking. Neither
    /// file reads nor the checker gate can block control admission.
    member _.BeginDemand(requested: int64, volatileContent: Map<string, string>) : Result<ProjectDemand<'View>, ProjectWorkspaceError> =
        let normalized = ProjectChecker.normalizeOverrides volatileContent |> Result.mapError ProjectWorkspaceError.CheckFailed
        match normalized with
        | Error error -> Error error
        | Ok overrides ->
            lock gate (fun () ->
                if closing then Error ProjectWorkspaceError.Closed
                elif requested <> revision || requested <= 0L then Error ProjectWorkspaceError.InvalidRevision
                elif nextDemand >= 65536UL then Error ProjectWorkspaceError.LifetimeLimitReached
                elif (AsyncMailbox.snapshot host).QueuedCommands + activeDemands > capacity - 4 then Error ProjectWorkspaceError.Busy
                else
                    let requestedGeneration =
                        match generation with
                        | Some value when value.Overrides <> overrides -> Error ProjectWorkspaceError.ConflictingInputs
                        | Some value -> Ok value
                        | None ->
                            let stamp = uint64 requested
                            admit (Action.SetInputs [{ Input = InputId 1UL; Stamp = InputStamp stamp; Value = ValueToken stamp }])
                            |> Result.bind (fun input ->
                                admit (Action.ReplaceScope(ScopeId 1UL, RevisionId stamp, [ScopeEntry.Define {
                                    Work = work requested; Stamp = DefinitionStamp stamp
                                    Reads = [{ Slot = ReadSlotId 1UL; Source = ReadSource.Input(InputId 1UL) }] }]))
                                |> Result.map (fun definition ->
                                    let value = { Revision = requested; Overrides = overrides; Prepared = None
                                                  Setup = [input; definition]; Output = None }
                                    generation <- Some value
                                    value))
                    requestedGeneration |> Result.bind (fun captured ->
                        nextDemand <- nextDemand + 1UL
                        let id = DemandId nextDemand
                        admit (Action.Demand(id, work requested)) |> Result.map (fun demandOperation ->
                            activeDemands <- activeDemands + 1
                            let mutable released = false
                            let mutable releaseOperation = None
                            let release () = async {
                                let operation = lock gate (fun () ->
                                    if not released then
                                        released <- true
                                        activeDemands <- activeDemands - 1
                                    match releaseOperation with
                                    | Some operation -> Ok(Some operation)
                                    | None when closing -> Ok None
                                    | None -> admit (Action.Release id) |> Result.map (fun operation ->
                                        releaseOperation <- Some operation
                                        Some operation))
                                match operation with
                                | Error error -> return Error error
                                | Ok None -> return Ok ()
                                | Ok(Some operation) -> return! WorkspaceProtocol.observe operation
                            }
                            let rec observeResult () = async {
                                // Capture the wake-up with its state before checking
                                // owner data, so a publication cannot be missed.
                                let snapshot, changed = AsyncMailbox.watch host
                                let result = lock gate (fun () ->
                                    if released then Some(Error ProjectWorkspaceError.Released)
                                    elif requested <> revision then Some(Error ProjectWorkspaceError.Superseded)
                                    elif closing then Some(Error ProjectWorkspaceError.Closed)
                                    else
                                        match AsyncMailbox.tryResult (work requested) host, captured.Output with
                                        | Some handle, Some(token, result) when handle.Value = token && AsyncMailbox.isEligible handle host -> Some result
                                        | _ -> None)
                                match result with
                                | Some result -> return result
                                | None when snapshot.IsClosing ->
                                    let! closed = AsyncMailbox.close host
                                    return Error(match closed with
                                                 | Ok () -> ProjectWorkspaceError.Closed
                                                 | Error failure -> ProjectWorkspaceError.HostFailed failure.Message)
                                | None ->
                                    match snapshot.Graph.Works |> List.tryFind (fun value -> value.Work = work requested) with
                                    | Some { Status = WorkStatus.Failed failure } ->
                                        return Error(if failure.Code = "ccs-check" then ProjectWorkspaceError.CheckFailed failure.Message
                                                     else ProjectWorkspaceError.HostFailed failure.Message)
                                    | Some { Status = WorkStatus.Cancelled } -> return Error ProjectWorkspaceError.Released
                                    | _ ->
                                        do! changed
                                        return! observeResult ()
                            }
                            let observe () = async {
                                let mutable failure = None
                                for operation in captured.Setup @ [demandOperation] do
                                    let! result = WorkspaceProtocol.observe operation
                                    match result with Error error -> failure <- Some error | Ok () -> ()
                                match failure with
                                | Some error -> return Error error
                                | None -> return! observeResult ()
                            }
                            ProjectDemand(requested, identity + ":" + string nextDemand, observe, release))))

    /// Convenience owns its demand. Cancellation stops observation and begins
    /// release; CloseAsync remains the physical drain boundary for compiler work.
    member this.CheckAsync(volatileContent: Map<string, string>) = async {
        let! reserved = this.ReserveAsync()
        match reserved with
        | Error error -> return Error error
        | Ok requested ->
            match this.BeginDemand(requested, volatileContent) with
            | Error error -> return Error error
            | Ok demand ->
                try
                    let! result = demand.ObserveAsync()
                    let! released = demand.ReleaseAsync()
                    return match released with Ok () -> result | Error error -> Error error
                finally
                    Async.Start(async { let! _ = demand.ReleaseAsync() in return () }, cancellationToken = CancellationToken.None)
    }

    /// Seals immediately. All later observations join the same physical close.
    member _.BeginClose() = lock gate (fun () ->
        closing <- true
        generation <- None
        AsyncMailbox.beginClose host)

    member this.CloseAsync() = async {
        let operation = this.BeginClose()
        let! result = AsyncMailbox.awaitClose operation
        return result |> Result.mapError (fun failure -> ProjectWorkspaceError.HostFailed failure.Message)
    }
