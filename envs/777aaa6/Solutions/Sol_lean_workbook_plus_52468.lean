-- Prove2me | solution 1 for lean_workbook_plus_52468
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:38:31.669323+00:00
-- url     : https://prove2.me/submissions/296c14d4-0067-4f55-8966-0713a3c8756b

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem positive_quartic_weighted_squares (x : ℝ) :
    2 * x ^ 4 + 12 * x ^ 3 - 7 * x + 2 =
      2 * x ^ 2 * (x - 1 / 2) ^ 2 +
      14 * x * (x - 3 / 7) ^ 2 +
      (23 / 2) * (x - 67 / 161) ^ 2 + 19 / 2254 := by
  ring

theorem positive_quartic_uniform_lower_bound (x : ℝ) (hx : 0 ≤ x) :
    19 / 2254 ≤ 2 * x ^ 4 + 12 * x ^ 3 - 7 * x + 2 := by
  rw [positive_quartic_weighted_squares]
  have h1 : 0 ≤ 2 * x ^ 2 * (x - 1 / 2) ^ 2 := by positivity
  have h2 : 0 ≤ 14 * x * (x - 3 / 7) ^ 2 := by positivity
  have h3 : 0 ≤ (23 / 2 : ℝ) * (x - 67 / 161) ^ 2 := by positivity
  linarith

theorem solution (x : ℝ) (hx : 0 < x) :
    2 * x ^ 4 + 12 * x ^ 3 - 7 * x + 2 > 0 := by
  linarith [positive_quartic_uniform_lower_bound x hx.le]

#print axioms solution
#print axioms positive_quartic_uniform_lower_bound
