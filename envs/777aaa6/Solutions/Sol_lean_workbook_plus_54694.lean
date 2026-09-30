-- Prove2me | solution 1 for lean_workbook_plus_54694
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:03:44.81885+00:00
-- url     : https://prove2.me/submissions/fc3914d2-3fca-4859-b832-f1f671cb893c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

noncomputable def octic_polynomial (x : ℝ) : ℝ :=
  60 * x ^ 8 + 135 * x ^ 7 + 369 * x ^ 6 + 169 * x ^ 5 + 402 * x ^ 4 +
    53 * x ^ 3 - 19 * x ^ 2 + 11 * x + 4

theorem octic_polynomial_remainder (x : ℝ) :
    212 * (octic_polynomial x - 4 - x) =
      x * (106 * x - 19) ^ 2 + 1759 * x + 12720 * x ^ 8 + 28620 * x ^ 7 +
        78228 * x ^ 6 + 35828 * x ^ 5 + 85224 * x ^ 4 := by
  unfold octic_polynomial
  ring

theorem octic_polynomial_lower_bound (x : ℝ) (hx : 0 ≤ x) :
    4 + x ≤ octic_polynomial x := by
  have hp : 0 ≤ x * (106 * x - 19) ^ 2 + 1759 * x + 12720 * x ^ 8 +
      28620 * x ^ 7 + 78228 * x ^ 6 + 35828 * x ^ 5 + 85224 * x ^ 4 := by
    positivity
  linarith [octic_polynomial_remainder x]

theorem octic_polynomial_minimum_iff (x : ℝ) (hx : 0 ≤ x) :
    octic_polynomial x = 4 ↔ x = 0 := by
  constructor
  · intro he
    linarith [octic_polynomial_lower_bound x hx]
  · rintro rfl
    unfold octic_polynomial
    ring

theorem solution (x : ℝ) (hx : x ≥ 0) :
    60 * x ^ 8 + 135 * x ^ 7 + 369 * x ^ 6 + 169 * x ^ 5 + 402 * x ^ 4 +
      53 * x ^ 3 - 19 * x ^ 2 + 11 * x + 4 ≥ 0 := by
  change 0 ≤ octic_polynomial x
  linarith [octic_polynomial_lower_bound x hx]

#print axioms solution
#print axioms octic_polynomial_minimum_iff
