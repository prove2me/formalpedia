-- Prove2me | solution 2 for Cryptography.IsogenySIDH.radicalTwoEval_exact_two_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T14:41:10.576279+00:00
-- url     : https://prove2.me/submissions/36265349-7e45-4214-b205-c0cacebb93c6

import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_DeepRadicalMontgomery
import Definitions.Def_Cryptography_IsogenySIDH_RadicalMontgomery
open Cryptography.IsogenySIDH in
theorem solution {K : Type*} [Field K] {A x y z w : K}
    (hx : x ≠ 0) (hbranch : x ^ 2 ≠ 1)
    (hP : OnMontgomery A (x, y)) (hz : z ≠ 0) :
    (OnMontgomery A (radicalTwoDeck (x, y)) ∧
      radicalTwoDeck (x, y) ≠ (x, y)) ∧
    (radicalTwoEval (z, w) = radicalTwoEval (x, y) ↔
      (z, w) = (x, y) ∨ (z, w) = radicalTwoDeck (x, y)) := by
  -- the fibre of the quotient map through `(x, y)`
  have hfib : radicalTwoEval (x, y) = radicalTwoEval (z, w) ↔
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
  have hP' : y ^ 2 = x ^ 3 + A * x ^ 2 + x := hP
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- the deck image stays on the curve
    show (-(y * x⁻¹ ^ 2)) ^ 2 = x⁻¹ ^ 3 + A * x⁻¹ ^ 2 + x⁻¹
    calc (-(y * x⁻¹ ^ 2)) ^ 2 = y ^ 2 * x⁻¹ ^ 4 := by ring
      _ = (x ^ 3 + A * x ^ 2 + x) * x⁻¹ ^ 4 := by rw [hP']
      _ = x⁻¹ ^ 3 + A * x⁻¹ ^ 2 + x⁻¹ := by field_simp; ring
  · -- and differs from `(x, y)` off the branch locus
    intro h
    have h1 : x⁻¹ = x := congrArg Prod.fst h
    apply hbranch
    have : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
    rw [h1] at this
    rw [sq]
    exact this
  · rw [eq_comm, hfib]
    simp only [radicalTwoDeck, Prod.mk.injEq]
