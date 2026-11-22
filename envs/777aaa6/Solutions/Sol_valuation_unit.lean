-- Prove2me | solution 1 for valuation_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:47:25.745698+00:00
-- url     : https://prove2.me/submissions/9f4472da-6351-4b9c-b769-246811963eac

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Theorems.Thm_valuation_eq_iff

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
theorem _root_.solution (a : Rˣ) : v a = 1 := by
  rw [← Valuation.map_one v, valuation_eq_iff]; use a; simp
