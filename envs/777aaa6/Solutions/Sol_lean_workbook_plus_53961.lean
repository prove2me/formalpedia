-- Prove2me | solution 1 for lean_workbook_plus_53961
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:37:12.550272+00:00
-- url     : https://prove2.me/submissions/b2738579-1c00-4a35-9577-66a329936c02

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem cyclotomic_cubic_gap (x : ℝ) :
    3 * (x ^ 2 - x + 1) ^ 3 - (x ^ 6 + x ^ 3 + 1) =
      (x - 1) ^ 4 * (2 * x ^ 2 - x + 2) := by
  ring

theorem cyclotomic_cubic_refinement (x : ℝ) :
    (15 / 8) * (x - 1) ^ 4 ≤
      3 * (x ^ 2 - x + 1) ^ 3 - (x ^ 6 + x ^ 3 + 1) := by
  rw [cyclotomic_cubic_gap]
  have hq : 15 / 8 ≤ 2 * x ^ 2 - x + 2 := by
    nlinarith [sq_nonneg (x - 1 / 4)]
  have hp : 0 ≤ (x - 1) ^ 4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hq hp]

theorem cyclotomic_cubic_equality (x : ℝ) :
    3 * (x ^ 2 - x + 1) ^ 3 = x ^ 6 + x ^ 3 + 1 ↔ x = 1 := by
  constructor
  · intro h
    have hp : (x - 1) ^ 4 = 0 := by
      have hn : 0 ≤ (x - 1) ^ 4 := by positivity
      nlinarith [cyclotomic_cubic_refinement x]
    have hz : x - 1 = 0 := by simpa using hp
    linarith
  · rintro rfl
    norm_num

theorem solution (x : ℝ) (hx : 0 < x) :
    3 * (x ^ 2 - x + 1) ^ 3 ≥ x ^ 6 + x ^ 3 + 1 := by
  have hp : 0 ≤ (x - 1) ^ 4 := by positivity
  linarith [cyclotomic_cubic_refinement x]

#print axioms solution
#print axioms cyclotomic_cubic_refinement
#print axioms cyclotomic_cubic_equality
