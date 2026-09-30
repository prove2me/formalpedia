-- Prove2me | solution 1 for lean_workbook_plus_73132
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:31:22.857397+00:00
-- url     : https://prove2.me/submissions/c415ac8b-f610-46c1-a7df-1d2b1b02b6a6

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

def sextic (x : ℝ) : ℝ :=
  9 * x ^ 6 - 90 * x ^ 5 + 431 * x ^ 4 - 1100 * x ^ 3 +
    1927 * x ^ 2 - 2394 * x + 2241

theorem sextic_lower_bound (x : ℝ) : 512 ≤ sextic x := by
  have hid : sextic x =
      (3 * x ^ 3 - 15 * x ^ 2 + 103 * x / 3 - 35 / 3) ^ 2 +
      (3584 / 9) * (x - 2) ^ 2 + 512 := by unfold sextic; ring
  rw [hid]
  nlinarith [sq_nonneg (3 * x ^ 3 - 15 * x ^ 2 + 103 * x / 3 - 35 / 3),
    sq_nonneg (x - 2)]

theorem quantitative_bound (x : ℝ) :
    512 * (x - 1) ^ 2 ≤ sextic x * (x - 1) ^ 2 :=
  mul_le_mul_of_nonneg_right (sextic_lower_bound x) (sq_nonneg _)

theorem sextic_unique_zero (x : ℝ) : sextic x * (x - 1) ^ 2 = 0 ↔ x = 1 := by
  constructor
  · intro h
    have hl := quantitative_bound x
    have hs := sq_nonneg (x - 1)
    nlinarith
  · rintro rfl
    simp

theorem solution : ∀ x : ℝ,
    (9 * x ^ 6 - 90 * x ^ 5 + 431 * x ^ 4 - 1100 * x ^ 3 +
      1927 * x ^ 2 - 2394 * x + 2241) * (x - 1) ^ 2 ≥ 0 := by
  intro x
  exact mul_nonneg (le_trans (by norm_num) (sextic_lower_bound x)) (sq_nonneg _)
