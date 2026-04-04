/-
Copyright (c) 2025. All rights reserved.
Author: Your Name
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: MKplusCAC.Prelim (add more as needed)
-- @axiom_system: none
-- @importance: medium

import MKplusCAC.Prelim
-- import MKplusCAC.OtherModule

-- Available from Prelim (no re-import needed):
--   ExistsUnique, ∃! x, p, ∃¹ x, p
--   ExistsUnique.intro / .exists / .choose / .choose_spec / .unique
--   choose_unique / choose_spec_unique / choose_uniq  (Peano-compatible)
--   Classical.*   (via open Classical in Prelim)

namespace MKplusCAC.ModuleName

-- ============================================================
-- Section 1: Definitions
-- ============================================================
-- Naming: UpperCamelCase for Prop predicates (IsXxx)
--         lowerCamelCase for functions/constructors

-- def myDef : Type := ...

-- ============================================================
-- Section 2: Basic Properties
-- ============================================================
-- Naming: subject_predicate pattern (snake_case)
--         Suffixes: _iff, _eq, _of_, _mem, _subset, _ne

-- theorem myTheorem : ... := by ...

-- ============================================================
-- Section 3: Advanced Theorems
-- ============================================================
-- Naming: conclusion_of_hypothesis pattern
--         Use .mp/.mpr for iff directions

-- ============================================================
-- Section 4: Exports
-- ============================================================

end MKplusCAC.ModuleName

export MKplusCAC.ModuleName (
  -- myDef
  -- myTheorem
)
