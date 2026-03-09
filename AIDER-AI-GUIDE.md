# AI Assistant Guide — Documentation Standards

**Last updated:** 2026-03-09 00:00
**Author**: Julián Calderón Almendros

This document establishes requirements and standards for technical documentation of this Lean 4 project.

---

## Requirements for REFERENCE.md

### (0.) **This documentation is technical, not user-facing.** It is a reference for AI assistants and experienced Lean 4 developers. Clear, precise, complete — but not pedagogical.

### (1.) **Lean modules**: List all `.lean` files in both root and subdirectories, with location, namespace, dependencies, and documentation status.

### (2.) **Module dependencies**: Each module must clearly document which modules it depends on, and which modules depend on it. Critical for AI navigation without loading the full project.

### (3.) **Namespaces and their relationships**: Namespaces are not necessarily equal to modules. Document which namespaces exist, which modules they belong to, and how they relate.

### (4.) **Introduced definitions**: For each module and namespace, document all definitions with location, dependencies, mathematical notation, and Lean 4 signature.

#### (4.1.) **How to document definitions**: Include the Lean 4 signature plus mathematical notation (no explanations — the audience is mathematicians and Lean 4 experts). Include module, namespace, and dependencies.

#### (4.2.) **Computability**: Indicate whether the definition is computable or noncomputable, and whether it has a boolean counterpart.

#### (4.3.) **Well-foundedness**: Indicate whether the definition includes a termination proof (*terminated by*).

#### (4.4.) **Notation**: Record introduced notation: infix/prefix/other, symbols used, priorities, so it can be used correctly in proofs and documentation.

### (5.) **Introduced axioms and their references**: Each axiom must document its location (module, namespace, declaration order) and relationship to definitions.

### (6.) For axioms and definitions, provide:

#### (6.1.) **Mathematical notation** (not Lean code) for human readability. No explanations — mathematical language suffices.

#### (6.2.) **Lean 4 signature** for correct usage in proofs and constructions.

#### (6.3.) **Dependencies** required to build the definition or axiom.

### (7.) Main theorems **without proof of any kind**, with reference to location (module, namespace, declaration order).

#### (7.1.) **Mathematical notation** (not Lean code).

#### (7.2.) **Lean 4 signature**.

#### (7.3.) **Dependencies** required to prove the theorem.

### (8.) **Nothing unproven goes in REFERENCE.md** — no pending theorems, no TODOs in this file. Only what is already proven or constructed in `.lean` files.

### (9.) **Update REFERENCE.md each time you load a `.lean` file** and find something new. Record the date and the last modification date of the `.lean` file for traceability.

### (10.) **REFERENCE.md must be self-sufficient** — enough to write new modules or documentation without loading the full project. This is the primary purpose of the file for AI assistants.

### (11.) **When reading a `.lean` file, add or verify its REFERENCE.md header comment** reminding the reader to project the file.

### (12.) **"Projecting" a `.lean` file into REFERENCE.md** means updating REFERENCE.md with all relevant information proven or constructed in that file, following the points above.

### (13.) **Relevant information** means all non-private definitions, notations, axioms, theorems, and any other content necessary to understand the project, use it as reference, or build further proofs.

### (14.) **Everything exportable in a `.lean` module must be projected into REFERENCE.md** and must appear in the module's export block.

---

## Timestamps

### (15.) All technical documentation files must include timestamps in `YYYY-MM-DD HH:MM` format (ISO 8601 abbreviated).

Applied to: REFERENCE.md, CHANGELOG.md, DEPENDENCIES.md, CURRENT-STATUS-PROJECT.md, and any technical summary file.

Purpose: Track how outdated a file is relative to REFERENCE.md, even within a single work session.

---

## Authorship and License

### (16.) All principal documentation files (README.md, REFERENCE.md, CURRENT-STATUS-PROJECT.md) must clearly state the author.

### (17.) Credits visible in README.md: educational resources, bibliographic references, AI tools used.

### (18.) License: MIT. Indicated in LICENSE, README.md, CURRENT-STATUS-PROJECT.md footer, and README.md badge.

### (19.) **All `.lean` files must include a copyright header** before any `import`:

```lean
/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
```

Placement: lines 1–5 of every `.lean` file, no exceptions (including the root module).

---

## File Locking System

### (20.) **At most one `.lean` file unlocked at any time.**

Tool: `git-lock.bash` in the project root.

```bash
bash git-lock.bash lock   MKplus/Module.lean   # lock
bash git-lock.bash unlock MKplus/Module.lean   # unlock
bash git-lock.bash list                             # show status
bash git-lock.bash init                             # install git hook
```

Work protocol:
1. **Session start**: Run `list`. If more than one file is unlocked, lock all except the target.
2. **Switching files**: Lock the current file **before** unlocking the next.
3. **Session end**: Lock **all** modified `.lean` files. Commit `locked_files.txt`.
4. **Pre-commit hook**: Blocks commits touching locked files. This is a safety net, not a substitute for the protocol.

Violation consequence: If more than one file is unlocked, lock all and restart with the correct file.

---

## Available Scripts

| Script | Purpose |
|--------|---------|
| `bash git-lock.bash lock/unlock/list/init` | File locking system |
| `bash new-module.bash ModuleName` | Create new module from template |
| `bash gen-root.bash` | Regenerate root import file |
| `bash check-sorry.bash` | Find all sorry statements |
| `bash update-toolchain.bash v4.x.x` | Update Lean toolchain with build verification |
| `make help` | Show all Makefile targets |

---

## Compliance

Verify that REFERENCE.md, `.lean` files, and documentation files comply with all points (0–20) before considering documentation complete and up to date.
