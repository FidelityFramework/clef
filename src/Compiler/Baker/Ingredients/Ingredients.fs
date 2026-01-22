// SPDX-License-Identifier: MIT

/// Baker Ingredients - The PUBLIC API for Recipes.
///
/// CRITICAL DISCIPLINE:
/// - Recipes ONLY call Ingredients. NEVER Primitives directly.
/// - Ingredients return Expanded<'a> for shadow AST integration.
/// - All primitives are wrapped, even single ones.
/// - Composite Ingredients encapsulate common patterns.
///
/// See: Serena memory "baker_ingredients_discipline"
module FSharp.Native.Compiler.Baker.Ingredients.Ingredients

open FSharp.Native.Compiler.NativeTypedTree.NativeTypes
open FSharp.Native.Compiler.NativeTypedTree.NativeGlobals
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Types
open FSharp.Native.Compiler.Baker.ShadowAST
open FSharp.Native.Compiler.Baker.Ingredients.RecipeBuilder
open FSharp.Native.Compiler.Baker.Ingredients.Primitives

//=============================================================================
// SHADOW HELPERS
//=============================================================================

/// Create an Expanded result with no shadow (for primitives that don't need tracking)
let private noShadow (value: 'a) : Expanded<'a> =
    { Value = value; Shadow = ShadowTree.Empty }

/// Create an Expanded result with a primitive shadow
let private withPrimitiveShadow (name: string) (value: 'a) : Expanded<'a> =
    { Value = value; Shadow = ShadowTree.Leaf (ShadowExpr.Primitive name) }

/// Create an Expanded result with a let-binding shadow
let private withLetShadow (name: string) (valueShadow: ShadowTree) (value: 'a) : Expanded<'a> =
    { Value = value; Shadow = ShadowTree.Node (ShadowExpr.Let (name, valueShadow), [valueShadow]) }

/// Compose multiple Expanded results into one
let private compose (shadows: Expanded<'a> list) (finalValue: 'b) : Expanded<'b> =
    let combinedShadow = 
        shadows 
        |> List.map (fun e -> e.Shadow) 
        |> ShadowTree.Sequence
    { Value = finalValue; Shadow = combinedShadow }

//=============================================================================
// LITERAL INGREDIENTS
//=============================================================================

/// True boolean literal
let trueValue : Recipe<Expanded<NodeId>> =
    recipe {
        let! id = boolLit true
        return withPrimitiveShadow "true" id
    }

/// False boolean literal
let falseValue : Recipe<Expanded<NodeId>> =
    recipe {
        let! id = boolLit false
        return withPrimitiveShadow "false" id
    }

/// Integer zero
let zeroInt : Recipe<Expanded<NodeId>> =
    recipe {
        let! id = intLit 0
        return withPrimitiveShadow "0" id
    }

/// Integer one
let oneInt : Recipe<Expanded<NodeId>> =
    recipe {
        let! id = intLit 1
        return withPrimitiveShadow "1" id
    }

/// Integer literal
let integerLit (n: int) : Recipe<Expanded<NodeId>> =
    recipe {
        let! id = intLit n
        return withPrimitiveShadow (string n) id
    }

/// Int64 literal
let integer64Lit (n: int64) : Recipe<Expanded<NodeId>> =
    recipe {
        let! id = int64Lit n
        return withPrimitiveShadow (string n) id
    }

//=============================================================================
// GUARD/CONDITIONAL INGREDIENTS
//=============================================================================

/// Always match (returns true)
let alwaysMatch : Recipe<Expanded<NodeId>> =
    trueValue

/// Combine a test with an optional guard using AND
/// If guard is None, just returns the test
let withOptionalGuard (test: NodeId) (guard: NodeId option) : Recipe<Expanded<NodeId>> =
    recipe {
        match guard with
        | Some guardId ->
            let! combined = andAlso test guardId
            return withPrimitiveShadow "guard && test" combined
        | None ->
            return noShadow test
    }

/// Select between two values based on comparison result
/// if cmp then a else b
let selectByComparison (cmp: NodeId) (ifTrue: NodeId) (ifFalse: NodeId) (resultType: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        let! result = ifThenElse cmp ifTrue ifFalse resultType
        return withPrimitiveShadow "if cmp then a else b" result
    }

/// Conditional expression
let conditional (cond: NodeId) (thenBranch: NodeId) (elseBranch: NodeId) (resultType: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        let! result = ifThenElse cond thenBranch elseBranch resultType
        return withPrimitiveShadow "if-then-else" result
    }

/// Wrap elements in a Sequential node
let wrapInSequence (elements: NodeId list) (resultType: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        match elements with
        | [] -> 
            // Empty sequence - return unit
            let! unitId = createAndEmit (SemanticKind.Literal NativeLiteral.Unit) Types.unitType
            return noShadow unitId
        | [single] ->
            // Single element - no wrapping needed
            return noShadow single
        | multiple ->
            let seqKind = SemanticKind.Sequential multiple
            let! seqId = createWithChildren seqKind resultType multiple
            return withPrimitiveShadow "sequential" seqId
    }

//=============================================================================
// LIST INGREDIENTS
//=============================================================================

/// Decompose a list into (head, tail, isEmpty) triple
let decomposeList (listId: NodeId) (elemType: NativeType) : Recipe<Expanded<NodeId * NodeId * NodeId>> =
    recipe {
        let! headId = head listId elemType
        let! tailId = tail listId elemType
        let! isEmptyId = isEmpty listId elemType
        return withPrimitiveShadow "decompose(head, tail, isEmpty)" (headId, tailId, isEmptyId)
    }

/// Create an empty list
let emptyListOf (elemType: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        let! id = emptyList elemType
        return withPrimitiveShadow "[]" id
    }

/// Prepend an element to a list
let prepend (headId: NodeId) (tailId: NodeId) (elemType: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        let! result = cons headId tailId elemType
        return withPrimitiveShadow "h :: t" result
    }

/// Conditionally prepend: if guard then h :: t else t
let conditionalPrepend (guard: NodeId) (headId: NodeId) (tailId: NodeId) (elemType: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        let! result = guardCons guard headId tailId elemType
        return withPrimitiveShadow "if p then h :: t else t" result
    }

/// Check if list is empty
let checkEmpty (listId: NodeId) (elemType: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        let! result = isEmpty listId elemType
        return withPrimitiveShadow "isEmpty" result
    }

/// Get head of list
let listHead (listId: NodeId) (elemType: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        let! result = head listId elemType
        return withPrimitiveShadow "head" result
    }

/// Get tail of list
let listTail (listId: NodeId) (elemType: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        let! result = tail listId elemType
        return withPrimitiveShadow "tail" result
    }

//=============================================================================
// APPLICATION INGREDIENTS
//=============================================================================

/// Apply a function to one argument
let applyOne (funcId: NodeId) (argId: NodeId) (resultType: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        let! result = app1 funcId argId resultType
        return withPrimitiveShadow "f x" result
    }

/// Apply a function to two arguments
let applyTwo (funcId: NodeId) (arg1Id: NodeId) (arg2Id: NodeId) (resultType: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        let! result = app2 funcId arg1Id arg2Id resultType
        return withPrimitiveShadow "f x y" result
    }

/// Apply a predicate (function returning bool)
let applyPredicate (predicateId: NodeId) (argId: NodeId) : Recipe<Expanded<NodeId>> =
    applyOne predicateId argId Types.boolType

/// Apply a mapper function
let applyMapper (mapperId: NodeId) (argId: NodeId) (outputType: NativeType) : Recipe<Expanded<NodeId>> =
    applyOne mapperId argId outputType

/// Apply a folder function (acc, elem) -> acc
let applyFolder (folderId: NodeId) (accId: NodeId) (elemId: NodeId) (accType: NativeType) : Recipe<Expanded<NodeId>> =
    applyTwo folderId accId elemId accType

//=============================================================================
// COMPOSITE INGREDIENTS: List Operations
//=============================================================================

/// Map an element and prepend to accumulator: cons (f h) acc
let mapAndPrepend (mapperId: NodeId) (headId: NodeId) (accId: NodeId) (outputElemType: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        let! mapped = applyMapper mapperId headId outputElemType
        let! result = prepend mapped.Value accId outputElemType
        return compose [mapped; result] result.Value
    }

/// Test predicate and conditionally prepend: if p h then h :: acc else acc
let filterAndPrepend (predicateId: NodeId) (headId: NodeId) (accId: NodeId) (elemType: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        let! test = applyPredicate predicateId headId
        let! result = conditionalPrepend test.Value headId accId elemType
        return compose [test; result] result.Value
    }

//=============================================================================
// UNION/PATTERN MATCH INGREDIENTS
//=============================================================================

/// Check if union tag equals expected index
let checkTag (scrutineeId: NodeId) (tagIndex: int) : Recipe<Expanded<NodeId>> =
    recipe {
        let! result = compareTagEq scrutineeId tagIndex
        return withPrimitiveShadow (sprintf "tag == %d" tagIndex) result
    }

/// Extract union payload (field at index 0)
let extractPayload (scrutineeId: NodeId) (payloadType: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        let! result = extractPayloadField scrutineeId 0 payloadType
        return withPrimitiveShadow "payload" result
    }

/// Extract union tag value
let extractTagValue (scrutineeId: NodeId) : Recipe<Expanded<NodeId>> =
    recipe {
        let! result = extractTag scrutineeId
        return withPrimitiveShadow "tag" result
    }

/// Create a let binding
let bindValue (name: string) (valueId: NodeId) (ty: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        let! bindingId = letBind name valueId ty
        return withLetShadow name ShadowTree.Empty bindingId
    }

/// Extract payload and bind to a name (composite)
let extractAndBindPayload (scrutineeId: NodeId) (name: string) (payloadType: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        let! payload = extractPayload scrutineeId payloadType
        let! binding = bindValue name payload.Value payloadType
        return compose [payload; binding] binding.Value
    }

/// Check tag and optionally extract/bind payload (composite)
let checkTagAndBind (scrutineeId: NodeId) (tagIndex: int) (payloadSpec: (string * NativeType) option) : Recipe<Expanded<NodeId * NodeId option>> =
    recipe {
        let! tagCheck = checkTag scrutineeId tagIndex
        match payloadSpec with
        | Some (name, ty) ->
            let! binding = extractAndBindPayload scrutineeId name ty
            return compose [tagCheck; binding] (tagCheck.Value, Some binding.Value)
        | None ->
            return { Value = (tagCheck.Value, None); Shadow = tagCheck.Shadow }
    }

//=============================================================================
// LITERAL COMPARISON INGREDIENTS
//=============================================================================

/// Compare scrutinee to a literal value
let matchesLiteral (scrutineeId: NodeId) (literal: NativeLiteral) (literalType: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        let! literalId = createAndEmit (SemanticKind.Literal literal) literalType
        let! result = compareEq scrutineeId literalId literalType
        return withPrimitiveShadow "== literal" result
    }

/// Equality comparison
let areEqual (leftId: NodeId) (rightId: NodeId) (ty: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        let! result = eq leftId rightId ty
        return withPrimitiveShadow "a == b" result
    }

/// Less-than comparison
let isLessThan (leftId: NodeId) (rightId: NodeId) (ty: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        let! result = lt leftId rightId ty
        return withPrimitiveShadow "a < b" result
    }

/// Greater-than comparison
let isGreaterThan (leftId: NodeId) (rightId: NodeId) (ty: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        let! result = gt leftId rightId ty
        return withPrimitiveShadow "a > b" result
    }

//=============================================================================
// ARITHMETIC INGREDIENTS
//=============================================================================

/// Add two values
let addValues (leftId: NodeId) (rightId: NodeId) (ty: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        let! result = add leftId rightId ty
        return withPrimitiveShadow "a + b" result
    }

/// Increment by one
let increment (valueId: NodeId) (ty: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        let! one = oneInt
        let! result = addValues valueId one.Value ty
        return compose [one; result] result.Value
    }

//=============================================================================
// OPTION INGREDIENTS
//=============================================================================

/// Create None value
let noneOf (elemType: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        let! result = none elemType
        return withPrimitiveShadow "None" result
    }

/// Create Some value
let someOf (valueId: NodeId) (elemType: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        let! result = some valueId elemType
        return withPrimitiveShadow "Some x" result
    }

/// Check if option is Some
let checkIsSome (optionId: NodeId) (elemType: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        let! result = isSome optionId elemType
        return withPrimitiveShadow "isSome" result
    }

/// Check if option is None
let checkIsNone (optionId: NodeId) (elemType: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        let! result = isNone optionId elemType
        return withPrimitiveShadow "isNone" result
    }

/// Get value from option (unsafe)
let getOptionValue (optionId: NodeId) (elemType: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        let! result = optionGet optionId elemType
        return withPrimitiveShadow "Option.get" result
    }

//=============================================================================
// BINDING INGREDIENTS
//=============================================================================

/// Create a pattern binding (for lambda parameters)
let declareParam (name: string) (ty: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        let! paramId = patternBinding name ty
        do! bindVariable name paramId ty
        return withPrimitiveShadow (sprintf "param:%s" name) paramId
    }

/// Create a variable reference
let referenceVar (name: string) (targetId: NodeId option) (ty: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        let! refId = varRef name targetId ty
        return withPrimitiveShadow (sprintf "ref:%s" name) refId
    }

/// Create a recursive let binding
let bindRecursive (name: string) (valueId: NodeId) (ty: NativeType) : Recipe<Expanded<NodeId>> =
    recipe {
        let! bindingId = letRecBind name valueId ty
        return withLetShadow name ShadowTree.Empty bindingId
    }
