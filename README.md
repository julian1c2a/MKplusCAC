# MKplusCAC

[![Lean 4](https://img.shields.io/badge/Lean-v4.28.0-blue)](https://leanprover.github.io/)
[![Build Status](https://img.shields.io/badge/build-passing-brightgreen)](CURRENT-STATUS-PROJECT.md)
[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)

> **Status**: See [CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md) for complete details.

Una implementación formal de la **Teoría de Conjuntos de Morse-Kelley con el Principio de Elección de Clases (CAC)** en Lean 4, sin dependencias de Mathlib.

## Description

Este proyecto construye los fundamentos de la teoría de conjuntos basándose en los axiomas de Morse-Kelley. Se diferencia de otras aproximaciones al evitar Mathlib por completo, priorizando la creación de una jerarquía de módulos autocontenida que culmina con la implementación robusta del Principio de Elección de Clases (Class Axiom of Choice).

## Modules

| Module | Namespace | Dependencies | Status |
|--------|-----------|--------------|--------|
| `Prelim.lean` | `MKplusCAC.Prelim` | — | 🧊 Frozen (Locked) |
| `MKplusCACAxioms.lean` | `MKplusCAC.MKplusCACAxioms` | `Prelim.lean` | 🔄 In progress (Locked) |

## Project Structure

```text
MKplusCAC/
├── MKplusCAC/
│   ├── Prelim.lean              # Preliminary definitions (ExistsUnique)
│   ├── MKplusCACAxioms.lean     # Axioms of Morse-Kelley + CAC
│   └── _template.lean           # Module template
└── MKplusCAC.lean               # Root module (auto-generated)
```

## Installation

```bash
git clone https://github.com/julian1c2a/MKplusCAC.git
cd MKplusCAC
lake build
```

## Requirements

- **Lean 4**: v4.28.0 or later
- **Lake**: Included with Lean 4

## Development Workflow

```bash
# Initialize lock system (first time only)
bash git-lock.bash init

# Create a new module
bash new-module.bash ModuleName

# Build
make build

# Check for sorry
make sorry

# Show locked files and sorry status
make status

# Regenerate root import file
bash gen-root.bash
```

## Documentation

- **[WORKFLOW.md](WORKFLOW.md)** — ⭐ **Complete development workflow** (start here after setup)
- **[REFERENCE.md](REFERENCE.md)** — Technical reference for all definitions and theorems
- **[AI-GUIDE.md](AI-GUIDE.md)** — Documentation standards and AI assistant guide
- **[NAMING-CONVENTIONS.md](NAMING-CONVENTIONS.md)** — Naming conventions (Mathlib style)
- **[CHANGELOG.md](CHANGELOG.md)** — Change history
- **[DEPENDENCIES.md](DEPENDENCIES.md)** — Module dependency diagrams
- **[DECISIONS.md](DECISIONS.md)** — Design decision records
- **[CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md)** — Current project status
- **[NEXT-STEPS.md](NEXT-STEPS.md)** — Planning and upcoming phases

## License

This project is under the MIT License. See [LICENSE](LICENSE) for details.

---

**Author**: Julián Calderón Almendros
*Last updated: 2026-04-04 00:00*
