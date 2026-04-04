# Design Decisions — MKplusCAC

**Last updated:** 2026-03-09 00:00
**Author**: Julián Calderón Almendros

Architectural Decision Records (ADR) for this project.
Each entry records *what* was decided and *why*, for future reference.

---

## ADR-001: No Mathlib dependency

**Date**: 2025-01-01
**Status**: Accepted

**Decision**: This project does not depend on Mathlib.

**Rationale**: [Explain why — e.g., educational goals, performance, avoiding API churn, etc.]

**Consequences**: All necessary infrastructure (ExistsUnique, etc.) must be built from scratch.

---

## ADR-002: autoImplicit = false

**Date**: 2025-01-01
**Status**: Accepted

**Decision**: `moreServerArgs := #["-DautoImplicit=false"]` is set in `lakefile.lean`.

**Rationale**: Explicit type annotations prevent accidental universe polymorphism issues and make code easier to read and maintain.

**Consequences**: All variables must be explicitly declared or annotated.

---

## ADR-003: File locking system

**Date**: 2025-01-01
**Status**: Accepted

**Decision**: Use `git-lock.bash` + `locked_files.txt` + pre-commit hook to prevent accidental edits to completed modules.

**Rationale**: Lean 4 proofs are fragile — small changes to completed modules can break dependent proofs. The locking system makes this explicit.

**Consequences**: Workflow requires locking/unlocking files. See AIDER-AI-GUIDE.md §20.

---

## Template for new decisions:

## ADR-NNN: [Title]

**Date**: YYYY-MM-DD
**Status**: [Proposed | Accepted | Deprecated | Superseded by ADR-XXX]

**Context**: [Why is this decision needed?]

**Decision**: [What was decided?]

**Rationale**: [Why this choice over alternatives?]

**Consequences**: [What are the trade-offs?]
