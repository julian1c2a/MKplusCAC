# Dependency Diagram — MKplusCAC

**Last updated:** 2025-01-01 00:00
**Author**: Your Name

## Project Structure

```
MKplusCAC/
├── Prelim.lean         # Preliminary definitions
├── _template.lean      # Module template (not imported)
├── Core/               # (subdirectory example)
│   └── Basic.lean
└── Topic/              # (subdirectory example)
    ├── Basic.lean
    └── Advanced.lean
MKplusCAC.lean        # Root module
```

## Dependency Graph

```mermaid
graph TD
    P[Prelim.lean]
    Z[MKplusCAC.lean] --> P
```

*(Update this diagram as modules are added. Use subdirectory grouping:)*

```mermaid
graph TD
    subgraph Core
        CB[Core.Basic]
    end
    subgraph Topic
        TB[Topic.Basic]
        TA[Topic.Advanced]
    end
    P[Prelim.lean]
    CB --> P
    TB --> P
    TB --> CB
    TA --> TB
    Z[MKplusCAC.lean] --> P
    Z --> CB
    Z --> TB
    Z --> TA
```

## Namespace Hierarchy

### 1. **MKplusCAC** (root)

```lean
-- MKplusCAC.lean imports all modules
```

### 2. **MKplusCAC.Prelim**

```lean
namespace MKplusCAC.Prelim
  -- Preliminary definitions
```

*(Add sub-namespaces as subdirectories are created)*

## Dependencies by Level

### Level 0: Foundations

- `Prelim.lean` — no dependencies

### Level 1: Core

- *(modules that depend only on Prelim)*

### Level 2: Derived

- *(modules that depend on Level 1)*

### Level N: Root

- `MKplusCAC.lean` — imports all modules

## Exports by Module

### Prelim.lean

```lean
export MKplusCAC.Prelim (
  -- exported names here
)
```

## Design Notes

1. **Separation of concerns**: each module handles one aspect
2. **Minimal dependencies**: only import what is strictly needed
3. **Selective exports**: only public definitions and theorems are exported
4. **No Mathlib** (unless explicitly required — add to lakefile.lean)
5. **One namespace per module**: mirrors file path (see ADR-005)

## Verification Commands

```bash
make build          # build full project
make sorry          # check for sorry
make status         # lock status + sorry
```
