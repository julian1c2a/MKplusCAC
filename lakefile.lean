import Lake
open Lake DSL

-- Replace «MKplusCAC» with your project name (must match directory name)
-- and update the package name accordingly
package «MKplusCAC» where
  -- Disable auto-implicit to enforce explicit type annotations everywhere
  moreServerArgs := #["-DautoImplicit=false"]

-- ── External dependencies (uncomment as needed) ──────────────────────────────

-- ZfcSetTheory: ZFC set theory in Lean 4, no Mathlib
-- Provides: SetUniverse, ExistsUnique, all ZFC axioms + constructions
-- require ZfcSetTheory from git
--   "https://github.com/julian1c2a/ZfcSetTheory" @ "master"

-- PeanoNatLib: Peano natural numbers, no Mathlib
-- Provides: Peano.ℕ₀, Peano.Add, Peano.Mul, Peano.StrictOrder, ...
-- require peanolib from git
--   "https://github.com/julian1c2a/Peano" @ "master"

-- Other dependency template:
-- require somedep from git
--   "https://github.com/user/repo" @ "main"

-- ─────────────────────────────────────────────────────────────────────────────

@[default_target]
lean_lib «MKplusCAC» where
  -- globs := #[.submodules `MKplusCAC]
  -- ↑ Uncomment to auto-discover all .lean files in MKplusCAC/
  --   (Lake will compile them without listing in the root file)
  --   Leave commented to use explicit imports in MKplusCAC.lean
