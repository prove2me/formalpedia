-- Prove2me | solution 1 for lean_workbook_plus_69178
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:08:05.68604+00:00
-- url     : https://prove2.me/submissions/5a0580a6-49be-40ee-a429-183ab1e70d1f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c x y z : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    a^2 / x + b^2 / y + c^2 / z ≥ (a + b + c)^2 / (x + y + z) := by
  have hS : 0 < x + y + z := by positivity
  have hid : a^2 / x + b^2 / y + c^2 / z - (a + b + c)^2 / (x + y + z) =
      (z*(a*y-b*x)^2 + x*(b*z-c*y)^2 + y*(c*x-a*z)^2) /
        (x*y*z*(x+y+z)) := by
    field_simp [ne_of_gt hx, ne_of_gt hy, ne_of_gt hz, ne_of_gt hS] <;> ring
  have hp : 0 ≤ (z*(a*y-b*x)^2 + x*(b*z-c*y)^2 + y*(c*x-a*z)^2) /
      (x*y*z*(x+y+z)) := by positivity
  rw [← hid] at hp
  linarith

#print axioms solution
