-- Prove2me | solution 1 for valuation_irreducible_zpow_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:58:01.631064+00:00
-- url     : https://prove2.me/submissions/3cdf1a66-2fe2-4797-8e91-2f5805eceea2

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Theorems.Thm_valuation_lt_one_of_irreducible
import Theorems.Thm_exp_zero_of_zpow_eq_one


set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R]
include hϖ
omit [IsDiscreteValuationRing R]
theorem _root_.solution (n : ℤ) : v (ϖ.val ^ n) = 1 ↔ n = 0 := by
  constructor
  · intro h
    simp at h
    have : v ϖ < 1 := valuation_lt_one_of_irreducible ϖ hϖ
    exact exp_zero_of_zpow_eq_one this h
  · rintro rfl
    simp
