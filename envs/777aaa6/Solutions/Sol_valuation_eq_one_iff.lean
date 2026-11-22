-- Prove2me | solution 1 for valuation_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:50:11.574903+00:00
-- url     : https://prove2.me/submissions/c844c106-5d4d-47ad-bf2a-60cfa23c61f6

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Theorems.Thm_valuation_unit

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
theorem _root_.solution (a : R) : IsUnit a ↔ v a = 1 :=
  ⟨fun h => valuation_unit h.unit, fun h => by
    have ha : (a : K) ≠ 0 := by
      intro c
      rw [c, Valuation.map_zero] at h
      exact zero_ne_one h
    have ha' : (a : K)⁻¹ ∈ R := by rw [mem_subring_iff_integer, map_inv₀, h, inv_one]
    exact ⟨⟨a, ⟨(a : K)⁻¹, ha'⟩, by
      apply Subtype.ext
      change (a : K) * (a : K)⁻¹ = 1
      exact mul_inv_cancel₀ ha, by
      apply Subtype.ext
      change (a : K)⁻¹ * (a : K) = 1
      exact inv_mul_cancel₀ ha⟩, rfl⟩⟩
