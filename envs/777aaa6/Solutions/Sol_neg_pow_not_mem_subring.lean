-- Prove2me | solution 1 for neg_pow_not_mem_subring
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:57:12.124951+00:00
-- url     : https://prove2.me/submissions/941238ac-3ca0-4f9b-97ad-ef799037bf48

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Theorems.Thm_inv_irreducible_not_mem_subring

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
variable (ϖ : R) (hϖ : Irreducible ϖ)
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R]
include hϖ
omit [ValuationRing R] [IsDiscreteValuationRing ↥R] [IsFractionRing (↥R) K]
theorem _root_.solution (n : ℕ) (hn : n > 0) : ϖ.val ^ (- n : ℤ) ∉ R := by
  induction n with
  | zero => contradiction
  | succ n ih =>
      have hϖnzero : ϖ.val ≠ 0 := by
        simp only [ne_eq, ZeroMemClass.coe_eq_zero]
        exact hϖ.ne_zero
      simp
      rw [zpow_add₀ hϖnzero]
      simp only [Int.reduceNeg, zpow_neg, zpow_one, zpow_natCast]
      simp only [gt_iff_lt, zpow_neg, zpow_natCast] at ih
      by_cases hnz : n = 0
      · subst hnz
        simp only [pow_zero, inv_one, mul_one]
        exact inv_irreducible_not_mem_subring ϖ hϖ
      · have : (ϖ.val ^ n)⁻¹ ∉ R := by
          apply ih
          exact Nat.zero_lt_of_ne_zero hnz
        contrapose! this
        have : ϖ.val * ϖ.val⁻¹ * (ϖ.val ^ n)⁻¹ = (ϖ.val ^ n)⁻¹ := by field_simp
        rw [← this, mul_assoc]
        apply Subring.mul_mem
        exact ϖ.property
        assumption
