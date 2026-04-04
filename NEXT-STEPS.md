# Next Steps — MKplusCAC

**Last updated:** 2026-04-04 00:00
**Author**: Julián Calderón Almendros

> This file tracks planned development phases. Each phase includes
> objectives, modules to create, dependencies, and estimated complexity.

---

## Phase 1: Foundations

**Objective**: Establish core infrastructure in `Prelim.lean`.

**Modules**:
- [x] `Prelim.lean` — ExistsUnique, basic infrastructure

**Dependencies**: None (Level 0)
**Complexity**: Simple

---

## Phase 2: Core Axioms

**Objective**: Implement the fundamental axioms of Morse-Kelley set theory and the Class Axiom of Choice (CAC).

**Modules**:
- [x] `MKplusCACAxioms.lean` — Core axioms and basic class/set definitions

**Dependencies**: Phase 1 complete (`Prelim.lean`)
**Complexity**: Medium

---

## Phase 3: Naming Migration

**Objective**: Ensure all identifiers follow Mathlib naming conventions.

**Modules**: All existing modules (`Prelim.lean` and `MKplusCACAxioms.lean`)
**Reference**: [NAMING-CONVENTIONS.md](NAMING-CONVENTIONS.md)

**Steps**:
1. Audit all exported names against `NAMING-CONVENTIONS.md`.
2. Rename definitions: `UpperCamelCase` for Prop/Type, `lowerCamelCase` for functions.
3. Rename theorems: `subject_predicate` pattern with standard suffixes.
4. Verify full compilation after each rename batch.
5. Update `REFERENCE.md` with the new names.

**Dependencies**: Phase 2 substantially complete
**Complexity**: Medium (mechanical but requires full recompilation and structural review)

---

## Phase 4: First Derived Modules

**Objective**: Build the first domain-specific modules derived from the axioms (e.g., relations, functions, ordinals).

**Modules**:
- [ ] `Relations.lean` / `Functions.lean` (TBD)
- [ ] `Ordinals.lean` (TBD)

**Dependencies**: Phase 3 complete
**Complexity**: High

---

## Phase Status Summary

| Phase | Description | Status |
|-------|-------------|--------|
| 1 | Foundations | ✅ Complete |
| 2 | Core Axioms | 🔄 In progress |
| 3 | Naming Migration | ❌ Pending |
| 4 | First Derived Modules | ❌ Pending |
