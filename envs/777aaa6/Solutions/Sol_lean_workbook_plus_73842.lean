-- Prove2me | solution 1 for lean_workbook_plus_73842
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:00:18.672278+00:00
-- url     : https://prove2.me/submissions/e193f27c-c8b1-4b9e-9877-b6c17b005062

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    1 / (x + y) + 1 / (y + z) + 1 / (z + x) ≤
      (3 * (x + y + z)) / (2 * (x*y + y*z + z*x)) := by
  have hxy : 0 < x + y := by positivity
  have hyz : 0 < y + z := by positivity
  have hzx : 0 < z + x := by positivity
  have hQ : 0 < x*y + y*z + z*x := by positivity
  have hid : 3 * (x + y + z) / (2 * (x*y + y*z + z*x)) -
      (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) =
      (x*y*(x-y)^2 + y*z*(y-z)^2 + z*x*(z-x)^2 +
        x^2*(y-z)^2 + y^2*(z-x)^2 + z^2*(x-y)^2) /
      (2 * (x*y + y*z + z*x) * (x+y) * (y+z) * (z+x)) := by
    field_simp [ne_of_gt hxy, ne_of_gt hyz, ne_of_gt hzx, ne_of_gt hQ] <;> ring
  have hp : 0 ≤ (x*y*(x-y)^2 + y*z*(y-z)^2 + z*x*(z-x)^2 +
        x^2*(y-z)^2 + y^2*(z-x)^2 + z^2*(x-y)^2) /
      (2 * (x*y + y*z + z*x) * (x+y) * (y+z) * (z+x)) := by positivity
  rw [← hid] at hp
  linarith

#print axioms solution
