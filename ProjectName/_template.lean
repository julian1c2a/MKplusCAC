/-
Copyright (c) 2025. All rights reserved.
Author: Your Name
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AIDER-AI-GUIDE.md §12 for the "proyectar" protocol.
-- Dependencies: ProjectName.Prelim (add more as needed)

import ProjectName.Prelim
-- import ProjectName.OtherModule

-- Available from Prelim (no re-import needed):
--   ExistsUnique, ∃! x, p, ∃¹ x, p
--   ExistsUnique.intro / .exists / .choose / .choose_spec / .unique
--   choose_unique / choose_spec_unique / choose_uniq  (Peano-compatible)
--   Classical.*   (via open Classical in Prelim)

namespace ProjectName.ModuleName

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

end ProjectName.ModuleName

export ProjectName.ModuleName (
  -- myDef
  -- myTheorem
)
