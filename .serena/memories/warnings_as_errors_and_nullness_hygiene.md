# CCS Build Hygiene: Warnings-As-Errors and Nullness Discipline

Date: 2026-02-18

## Context
Clef.Compiler.Service is the compiler frontend for Composer. Build warnings are treated as correctness and maintainability signals, not cosmetic output.

## Standing Rule
- Keep `TreatWarningsAsErrors` enabled for `src/Compiler/Clef.Compiler.Service.fsproj`.
- Fix warnings at source; avoid warning debt accumulation.

## Nullness-Specific Rule
- Nullness warnings are roadmap blockers for self-hosting and should be resolved immediately.
- At BCL/API boundaries that may return null, normalize to option and handle exhaustively.
- Prefer explicit non-null types internally and avoid defensive null checks on non-nullable values.

## Demarcation (Bridge Mode)
- Internal CCS/Composer compiler code remains `.fs` during `dotnet` bootstrap.
- External project authoring may adopt `.clef` without forcing internal extension migration.
