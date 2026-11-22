-- Prove2me | solution 1 for inv_irreducible_not_mem_subring
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:55:19.839182+00:00
-- url     : https://prove2.me/submissions/35386657-3af3-4fcf-b7c2-0c9db4e42746

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R]
include hϖ
omit [ValuationRing R] [IsDiscreteValuationRing ↥R] [IsFractionRing (↥R) K]
theorem _root_.solution : ϖ.val⁻¹ ∉ R := by
  by_contra h
  apply hϖ.not_isUnit
  have hϖnzero : ϖ.val ≠ 0 := by
    simp only [ne_eq, ZeroMemClass.coe_eq_zero]
    exact hϖ.ne_zero
  let x : Rˣ := ⟨ϖ, ⟨ϖ.val⁻¹, h⟩, by
    apply Subtype.ext
    change ϖ.val * ϖ.val⁻¹ = 1
    exact mul_inv_cancel₀ hϖnzero, by
    apply Subtype.ext
    change ϖ.val⁻¹ * ϖ.val = 1
    exact inv_mul_cancel₀ hϖnzero⟩
  use x
