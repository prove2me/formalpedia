-- Prove2me | solution 1 for lean_workbook_plus_56540
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:28:08.230197+00:00
-- url     : https://prove2.me/submissions/00e4267b-17d4-4102-ab61-141f3702f01b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

theorem quartic_constraint_norm_identity (x y : ℝ)
    (h : x * y * (x ^ 2 - y ^ 2) = x ^ 2 + y ^ 2) :
    (x ^ 2 + y ^ 2) * (x ^ 2 + y ^ 2 - 4) =
      (x ^ 2 - y ^ 2 - 2 * x * y) ^ 2 := by nlinarith [h]

theorem quartic_constraint_sharp_norm (x y : ℝ) (hx : x ≠ 0)
    (h : x * y * (x ^ 2 - y ^ 2) = x ^ 2 + y ^ 2) :
    4 ≤ x ^ 2 + y ^ 2 := by
  have hp : 0 < x ^ 2 + y ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg y)
  have hi := quartic_constraint_norm_identity x y h
  nlinarith [sq_nonneg (x ^ 2 - y ^ 2 - 2 * x * y)]

theorem quartic_constraint_norm_equality (x y : ℝ) (hx : x ≠ 0)
    (h : x * y * (x ^ 2 - y ^ 2) = x ^ 2 + y ^ 2) :
    x ^ 2 + y ^ 2 = 4 ↔ x ^ 2 - y ^ 2 = 2 * x * y := by
  have hi := quartic_constraint_norm_identity x y h
  have hb := quartic_constraint_sharp_norm x y hx h
  constructor
  · intro he
    have hz : (x ^ 2 - y ^ 2 - 2 * x * y) ^ 2 = 0 := by rw [← hi, he]; norm_num
    nlinarith [sq_eq_zero_iff.mp hz]
  · intro he
    rw [he, sub_self, zero_pow (by decide : 2 ≠ 0)] at hi
    nlinarith

theorem quartic_constraint_norm_attainment :
    ∃ x y : ℝ, x ≠ 0 ∧ x * y * (x ^ 2 - y ^ 2) = x ^ 2 + y ^ 2 ∧
      x ^ 2 + y ^ 2 = 4 := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  have hlow : 0 ≤ 2 - Real.sqrt 2 := by nlinarith
  have hx : (Real.sqrt (2 + Real.sqrt 2)) ^ 2 = 2 + Real.sqrt 2 :=
    Real.sq_sqrt (by positivity)
  have hy : (Real.sqrt (2 - Real.sqrt 2)) ^ 2 = 2 - Real.sqrt 2 :=
    Real.sq_sqrt hlow
  have hxy : Real.sqrt (2 + Real.sqrt 2) * Real.sqrt (2 - Real.sqrt 2) = Real.sqrt 2 := by
    rw [← Real.sqrt_mul (by positivity), show (2 + Real.sqrt 2) * (2 - Real.sqrt 2) = 2 by nlinarith]
  refine ⟨Real.sqrt (2 + Real.sqrt 2), Real.sqrt (2 - Real.sqrt 2), ?_, ?_, ?_⟩
  · exact ne_of_gt (Real.sqrt_pos.2 (by positivity))
  · rw [hxy, hx, hy]
    nlinarith
  · rw [hx, hy]
    ring

theorem solution (x y : ℝ) (h₁ : x ≠ 0)
    (h₂ : x * y * (x^2 - y^2) = x^2 + y^2) : x^2 + y^2 >= 0 := by
  linarith [quartic_constraint_sharp_norm x y h₁ h₂]

#print axioms solution
#print axioms quartic_constraint_norm_identity
#print axioms quartic_constraint_sharp_norm
#print axioms quartic_constraint_norm_equality
#print axioms quartic_constraint_norm_attainment
