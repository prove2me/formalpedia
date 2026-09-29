-- Prove2me | solution 1 for lean_workbook_plus_22121
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-03-15T15:11:44.580065+00:00
-- url     : https://prove2.me/submissions/7983afb9-7ada-4e70-b303-a3103c808f55

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Data.Real.Basic

theorem solution (a b : ℝ) (hab : 0 < a ∧ 0 < b) (h : a * b + b ^ 2 = 2 * a) : (a - b) * (a * b + 2 * b - 3) ≥ 0 := by
  have ha := hab.1
  have hb := hab.2
  have hb2 : b < 2 := by nlinarith [sq_nonneg b]
  have h2b : (0 : ℝ) < 2 - b := by linarith
  have h_ab : (a - b) * (2 - b) = 2 * b * (b - 1) := by linear_combination -h
  have h_abc : (a * b + 2 * b - 3) * (2 - b) = (b - 1) * (b ^ 2 - b + 6) := by
    linear_combination (-b) * h
  have key : (a - b) * (a * b + 2 * b - 3) * ((2 - b) * (2 - b)) =
    2 * b * (b - 1) ^ 2 * (b ^ 2 - b + 6) := by
    have : (a - b) * (a * b + 2 * b - 3) * ((2 - b) * (2 - b)) =
      ((a - b) * (2 - b)) * ((a * b + 2 * b - 3) * (2 - b)) := by ring
    rw [this, h_ab, h_abc]; ring
  have hq : (0 : ℝ) ≤ b ^ 2 - b + 6 := by nlinarith [sq_nonneg (b - 1 / 2)]
  have rhs_nn : (0 : ℝ) ≤ 2 * b * (b - 1) ^ 2 * (b ^ 2 - b + 6) :=
    mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * b) (sq_nonneg (b - 1))) hq
  by_contra h_neg
  push_neg at h_neg
  have h_prod_neg : (a - b) * (a * b + 2 * b - 3) * ((2 - b) * (2 - b)) < 0 :=
    mul_neg_of_neg_of_pos h_neg (mul_pos h2b h2b)
  linarith

-- Auto-generated type check: solution must match the target
theorem _type_check_target (a b : ℝ) (hab : 0 < a ∧ 0 < b) (h : a * b + b ^ 2 = 2 * a) : (a - b) * (a * b + 2 * b - 3) ≥ 0   := by apply solution; repeat assumption
