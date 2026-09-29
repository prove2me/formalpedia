-- Prove2me | solution 1 for ArithmeticVCDim.ratArithHeight_inv
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:09:33.815454+00:00
-- url     : https://prove2.me/submissions/10c5d0a1-90ef-4ce6-a5b5-f9efdc83a3d3

-- Sol generated from Bridges/PosetTheory/ArithmeticVCDimension.lean
import Mathlib
import Definitions.Def_Bridges_PosetTheory_ArithmeticVCDimension

/-!
# The rational arithmetic height

This module supplies the arithmetic height used by
`Bridges/TropicalAlgebra/TropicalArithmeticUltrametric.lean`.

`ratArithHeight q = |num q| + den q` is the naive additive height of a rational number in
lowest terms.  It is the basic complexity measure attached to a rational datum: the
number of bits needed to write it down, up to a constant.  The file records its
elementary properties; the *failure* of the ultrametric inequality for this height —
the reason a genuine valuation is needed instead — is proved downstream in
`TropicalArithmeticUltrametric.ratArithHeight_not_nonarchimedean`.
-/

open ArithmeticVCDim









open ArithmeticVCDim in
theorem solution(q : ℚ) (hq : q ≠ 0) :
    ratArithHeight q⁻¹ = ratArithHeight q := by
  have hnum : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have hsign : q.num.sign.natAbs = 1 := by
    rcases lt_trichotomy q.num 0 with h | h | h
    · rw [Int.sign_eq_neg_one_of_neg h]; rfl
    · exact absurd h hnum
    · rw [Int.sign_eq_one_of_pos h]; rfl
  have hnum' : (q⁻¹).num.natAbs = q.den := by
    simp [Rat.num_inv, Int.natAbs_mul, hsign]
  have hden : (q⁻¹).den = q.num.natAbs := Rat.den_inv_of_ne_zero hq
  simp only [ratArithHeight, hnum', hden]
  omega
