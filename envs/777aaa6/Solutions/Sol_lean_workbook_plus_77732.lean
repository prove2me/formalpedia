-- Prove2me | solution 1 for lean_workbook_plus_77732
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:13:53.325277+00:00
-- url     : https://prove2.me/submissions/0c7345c4-498b-4558-a1e7-5bede2ffa472

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x / y + y / z + z / x ≥
      z * (x + y) / (y * (y + z)) + x * (y + z) / (z * (z + x)) +
        y * (z + x) / (x * (x + y)) := by
  have hxy : 0 < x + y := by positivity
  have hyz : 0 < y + z := by positivity
  have hzx : 0 < z + x := by positivity
  have hid : x / y + y / z + z / x -
      (z * (x + y) / (y * (y + z)) + x * (y + z) / (z * (z + x)) +
        y * (z + x) / (x * (x + y))) =
      ((x - z) ^ 2 * (2 * x + z) + (y - x) ^ 2 * (2 * y + x) +
        (z - y) ^ 2 * (2 * z + y)) / (3 * (x + y) * (y + z) * (z + x)) := by
    field_simp [ne_of_gt hx, ne_of_gt hy, ne_of_gt hz,
      ne_of_gt hxy, ne_of_gt hyz, ne_of_gt hzx] <;> ring
  have hn : 0 ≤ ((x - z) ^ 2 * (2 * x + z) + (y - x) ^ 2 * (2 * y + x) +
      (z - y) ^ 2 * (2 * z + y)) / (3 * (x + y) * (y + z) * (z + x)) := by positivity
  linarith

#print axioms solution
