// SPDX-License-Identifier: MIT
/// The source owner supplies admitted storage accesses and one producer call.
/// This ingredient constructs the shared successful-result protocol as PSG
/// structure. It grants no demand, residence, concurrency or source-type rule.
module Clef.Compiler.Baker.Ingredients.Memoization

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives
module C = Clef.Compiler.Baker.Ingredients.Continuations

type Access = {
    NamePrefix: string
    EnvironmentType: NativeType
    ResultType: NativeType
    Environment: SaturationParser<NodeId>
    ReadComputed: NodeId -> SaturationParser<NodeId>
    ReadCached: NodeId -> SaturationParser<NodeId>
    Invoke: NodeId -> SaturationParser<NodeId>
    StoreCached: NodeId -> NodeId -> SaturationParser<NodeId>
    PublishComputed: NodeId -> NodeId -> SaturationParser<NodeId>
}

type Force = {
    EnvironmentBinding: NodeId
    Condition: NodeId
    CachedRead: NodeId
    Invocation: NodeId
    ResultBinding: NodeId
    Store: NodeId
    Publication: NodeId
    UncachedBranch: NodeId
    Conditional: NodeId
}

/// Snapshot the actual environment once. The cold branch computes, stores,
/// then publishes completion and returns that same value. The warm branch
/// reads only the previously published result; no default cache value exists.
let force (access: Access) = saturation {
    let environmentName = access.NamePrefix + "force_environment"
    let resultName = access.NamePrefix + "first_result"
    let! actualEnvironment = access.Environment
    let! environmentBinding = letBind environmentName actualEnvironment access.EnvironmentType
    let environmentRef () = varRef environmentName (Some environmentBinding) access.EnvironmentType
    let! conditionEnvironment = environmentRef ()
    let! condition = access.ReadComputed conditionEnvironment
    let! cachedEnvironment = environmentRef ()
    let! cachedRead = access.ReadCached cachedEnvironment
    let! invocationEnvironment = environmentRef ()
    let! invocation = access.Invoke invocationEnvironment
    let! resultBinding = letBind resultName invocation access.ResultType
    let! storedResult = varRef resultName (Some resultBinding) access.ResultType
    let! storeEnvironment = environmentRef ()
    let! store = access.StoreCached storeEnvironment storedResult
    let! published = boolLit true
    let! publishEnvironment = environmentRef ()
    let! publication = access.PublishComputed publishEnvironment published
    let! result = varRef resultName (Some resultBinding) access.ResultType
    let! uncached = C.block [resultBinding; store; publication; result] access.ResultType
    let! conditional = ifThenElse condition cachedRead uncached access.ResultType
    return {
        EnvironmentBinding = environmentBinding; Condition = condition; CachedRead = cachedRead
        Invocation = invocation; ResultBinding = resultBinding; Store = store
        Publication = publication; UncachedBranch = uncached; Conditional = conditional
    }
}
