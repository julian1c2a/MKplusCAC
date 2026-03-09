/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AIDER-AI-GUIDE.md §12 for the "proyectar" protocol.
-- Dependencies: MKplus.Prelim (add more as needed)

import MKplus.Prelim
-- import MKplus.OtherModule

-- Available from Prelim (no re-import needed):
--   ExistsUnique, ∃! x, p, ∃¹ x, p
--   ExistsUnique.intro / .exists / .choose / .choose_spec / .unique
--   choose_unique / choose_spec_unique / choose_uniq  (Peano-compatible)
--   Classical.*   (via open Classical in Prelim)

namespace MKplus.ModuleName

-- ============================================================
-- Section 1: Definitions
-- ============================================================

-- def myDef : Type := ...

-- ============================================================
-- Section 2: Theorems
-- ============================================================

-- theorem myTheorem : ... := by ...

-- ============================================================
-- Section 3: Exports
-- ============================================================

end MKplus.ModuleName

export MKplus.ModuleName (
  -- myDef
  -- myTheorem
)
