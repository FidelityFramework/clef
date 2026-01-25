# Unified Type Representation

> **Status**: Architectural Principle
> **Updated**: January 2026

## Core Principle

**Type constructors are recognized during construction, producing NativeType values directly with type variables preserved.**

## The Balance

| Concern | How Addressed |
|---------|---------------|
| Recognition | Type constructors identified during parsing/checking |
| Polymorphism | Type variables remain variables until monomorphization |
| Inference | Full Hindley-Milner with principal types |
| SRTP | Constraints collected during checking, resolved appropriately |

## Type Construction

When FNCS encounters `nativeptr<'T>`:

1. `nativeptr` recognized as NTU type constructor
2. `TNativePtr` value produced
3. `'T` preserved as `TVar`
4. Inference proceeds with full polymorphism

## Timing

| Operation | When |
|-----------|------|
| Type constructor recognition | During parsing/type checking |
| Type variable creation | During type checking |
| Constraint collection | During type checking |
| Constraint solving | During type checking |
| SRTP resolution | During constraint solving |
| Let-polymorphism | At let-binding generalization |
| Monomorphization | During PSG saturation (Baker) |
| Code generation | After saturation (Alex) |

## Influences

- **F***: Unified term representation where types are terms
- **Nanopass**: Explicit intermediate languages with justified transitions
- **Hindley-Milner**: Type variables, unification, principal types, let-polymorphism

## Specification Reference

See `fsnative-spec/spec/types-and-type-constraints.md` § "Unified Type Representation"
