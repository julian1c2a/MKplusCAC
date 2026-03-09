# Dependency Diagram — MKplus

**Last updated:** 2026-03-09 00:00
**Author**: Julián Calderón Almendros

## Project Structure

```
MKplus/
├── Prelim.lean         # Preliminary definitions
└── _template.lean      # Module template (not imported)
MKplus.lean        # Root module
```

## Dependency Graph

```mermaid
graph TD
    P[Prelim.lean]
    Z[MKplus.lean] --> P
```

## Namespace Hierarchy

### 1. **MKplus.Prelim**

```lean
namespace MKplus.Prelim
  -- Preliminary definitions
```

## Dependencies by Level

### Level 0: Foundations

- `Prelim.lean` — no dependencies

### Level N: Root

- `MKplus.lean` — imports all modules

## Exports by Module

### Prelim.lean

```lean
export MKplus.Prelim (
  -- exported names here
)
```

## Design Notes

1. **Separation of concerns**: each module handles one aspect
2. **Minimal dependencies**: only import what is strictly needed
3. **Selective exports**: only public definitions and theorems are exported
4. **No Mathlib** (unless explicitly required — add to lakefile.lean)

## Verification Commands

```bash
make build          # build full project
make sorry          # check for sorry
make status         # lock status + sorry
```
