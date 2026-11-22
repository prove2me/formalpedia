-- Prove2me | solution 1 for P2M_unit_mul_zpow_congr_zpow__8af5a51cd3a7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:55:17.988186+00:00
-- url     : https://prove2.me/submissions/2153b1c3-85c8-424c-bfde-f2a8dd22a697

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
theorem _root_.solution (a b : Rˣ) (m n : ℤ) (h : a * ϖ.val ^ m = b * ϖ.val ^ n) :
    m = n := by
  wlog hmn : m ≤ n
  · simp only [not_le] at hmn
    symm
    exact this ϖ hϖ b a n m h.symm (le_of_lt hmn)
  have h' : a * ϖ.val ^ m * ϖ.val ^ (-m) = b * ϖ.val ^ n * ϖ.val ^ (-m) :=
    congrFun (congrArg HMul.hMul h) (ϖ.val ^ (-m))
  rw [mul_assoc, mul_assoc, ← zpow_add₀, ← zpow_add₀] at h'
  simp at h'
  have : a * ϖ ^ 0 = b * ϖ ^ (Int.toNat (n - m)) := by
    ext
    simp [h']
    rw [← sub_eq_add_neg]
    nth_rw 1 [← Int.toNat_sub_of_le hmn]
    norm_cast
  have : 0 = Int.toNat (n - m) :=
    IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ a b 0 (Int.toNat (n - m)) this
  rw [← Nat.cast_inj (R := ℤ)] at this
  simp only [CharP.cast_eq_zero, Int.ofNat_toNat, right_eq_sup, tsub_le_iff_right, zero_add] at this
  symm
  exact Int.le_antisymm this hmn
  all_goals repeat simpa using hϖ.ne_zero
