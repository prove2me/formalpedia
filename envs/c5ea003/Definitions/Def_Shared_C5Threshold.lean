-- Prove2me | Definitions.Def_Shared_C5Threshold
-- name    : Shared_C5Threshold
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:34:45.433716+00:00
-- url     : https://prove2.me/theorems/8376307d-649d-49b2-a9f6-d189fe15b9b5
-- title:
--   Aether Catalog definitions — Shared_C5Threshold
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.C5Threshold`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/C5Threshold.lean by skeleton subtraction
import Mathlib

/-! # Generalized cycle-decomposition thresholds -/

namespace C5Decomp

/-- The generalized Nash--Williams threshold for a cycle of length `l`. -/
noncomputable def nwThreshold (l : ℕ) : ℝ := (l : ℝ) / (2 * (l : ℝ) - 2)



end C5Decomp


