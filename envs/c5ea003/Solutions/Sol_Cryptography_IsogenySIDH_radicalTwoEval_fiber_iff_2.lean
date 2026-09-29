-- Prove2me | solution 2 for Cryptography.IsogenySIDH.radicalTwoEval_fiber_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T14:36:29.420272+00:00
-- url     : https://prove2.me/submissions/2b0e27c3-bed6-49d9-8c71-1d51f625896f

import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_DeepRadicalMontgomery
import Definitions.Def_Cryptography_IsogenySIDH_RadicalMontgomery
open Cryptography.IsogenySIDH in
theorem solution {K : Type*} [Field K] {x y z w : K}
    (hx : x ≠ 0) (hz : z ≠ 0) (hbranch : x ^ 2 ≠ 1) :
    radicalTwoEval (x, y) = radicalTwoEval (z, w) ↔
      (z = x ∧ w = y) ∨ (z = x⁻¹ ∧ w = -(y * x⁻¹ ^ 2)) := by
  have hxx : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
  have hzz : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
  have h1x : 1 - x ^ 2 ≠ 0 := fun h => hbranch (by linear_combination -h)
  have h1xi : 1 - x⁻¹ ^ 2 ≠ 0 := by
    intro h
    apply hbranch
    have : x⁻¹ ^ 2 = 1 := by linear_combination -h
    rwa [inv_pow, inv_eq_one] at this
  constructor
  · intro h
    have e1 := congrArg Prod.fst h
    have e2 := congrArg Prod.snd h
    simp only [radicalTwoEval] at e1 e2
    -- `x + 1/x = z + 1/z` forces `z = x` or `z = 1/x`
    have key : (z - x) * (z - x⁻¹) = 0 := by linear_combination (-z) * e1 + hxx - hzz
    rcases mul_eq_zero.mp key with h' | h'
    · have hzx : z = x := sub_eq_zero.mp h'
      subst hzx
      left
      refine ⟨rfl, ?_⟩
      exact (mul_right_cancel₀ h1xi e2).symm
    · have hzx : z = x⁻¹ := sub_eq_zero.mp h'
      subst hzx
      right
      refine ⟨rfl, ?_⟩
      rw [inv_inv] at e2
      apply mul_right_cancel₀ h1x
      have hx2 : x ^ 2 * x⁻¹ ^ 2 = 1 := by rw [← mul_pow, hxx, one_pow]
      linear_combination -e2 - y * hx2
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · unfold radicalTwoEval
      refine Prod.ext ?_ ?_
      · simp only [inv_inv]
        ring
      · simp only [inv_inv]
        field_simp
        ring
