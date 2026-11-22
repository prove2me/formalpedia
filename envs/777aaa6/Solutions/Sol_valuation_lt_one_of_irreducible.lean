-- Prove2me | solution 1 for valuation_lt_one_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:52:45.955086+00:00
-- url     : https://prove2.me/submissions/1d277ea2-e568-4af9-9ebf-d5b6c0560868

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Theorems.Thm_valuation_eq_one_iff

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
include hϖ
theorem _root_.solution : v ϖ < 1 := by
  by_contra h
  apply hϖ.not_isUnit
  rw [valuation_eq_one_iff]
  apply le_antisymm
  · simp [← mem_subring_iff_integer]
  · simpa using h
