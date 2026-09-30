-- Prove2me | solution 1 for lean_workbook_plus_73957
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:15:30.649562+00:00
-- url     : https://prove2.me/submissions/456aaa5b-9832-4a39-aff8-5d7a4c319a03

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + 2 * b = 1) :
    (a + 1 / b) * (b + 1 / a) ≥ 81 / 8 := by
  have heq : (a + 2 * b) ^ 2 = 1 := by rw [hab]; norm_num
  have hp : a * b ≤ 1 / 8 := by nlinarith [sq_nonneg (a - 2 * b)]
  have hid : (a + 1 / b) * (b + 1 / a) - 81 / 8 =
      (1 - 8 * a * b) * (8 - a * b) / (8 * a * b) := by
    field_simp [ne_of_gt ha, ne_of_gt hb] <;> ring
  have hn : 0 ≤ (1 - 8 * a * b) * (8 - a * b) / (8 * a * b) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  linarith

#print axioms solution
