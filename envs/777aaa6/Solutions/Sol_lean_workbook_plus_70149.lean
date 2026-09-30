-- Prove2me | solution 1 for lean_workbook_plus_70149
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:04:27.044545+00:00
-- url     : https://prove2.me/submissions/926879d3-76ad-4597-a1f2-3a779d25d9c1

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x^2 / (x^2 + x*y + y^2) + y^2 / (y^2 + y*z + z^2) +
      z^2 / (z^2 + z*x + x^2) ≥ 1 := by
  have hA : 0 < x^2 + x*y + y^2 := by positivity
  have hB : 0 < y^2 + y*z + z^2 := by positivity
  have hC : 0 < z^2 + z*x + x^2 := by positivity
  have hid : x^2 / (x^2 + x*y + y^2) + y^2 / (y^2 + y*z + z^2) +
      z^2 / (z^2 + z*x + x^2) - 1 =
      ((y*(x^2-y*z))^2 + (z*(y^2-z*x))^2 + (x*(z^2-x*y))^2) /
      (2*(x^2+x*y+y^2)*(y^2+y*z+z^2)*(z^2+z*x+x^2)) := by
    field_simp [ne_of_gt hA, ne_of_gt hB, ne_of_gt hC] <;> ring
  have hp : 0 ≤ ((y*(x^2-y*z))^2 + (z*(y^2-z*x))^2 + (x*(z^2-x*y))^2) /
      (2*(x^2+x*y+y^2)*(y^2+y*z+z^2)*(z^2+z*x+x^2)) := by positivity
  rw [← hid] at hp
  linarith

#print axioms solution
