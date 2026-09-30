-- Prove2me | solution 1 for lean_workbook_plus_13220
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:19:36.574825+00:00
-- url     : https://prove2.me/submissions/db8df1a6-2344-4eb1-8660-d8220d429621

import Mathlib

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (z + x) / y + (x + y) / z ≥
      4 * x / (y + z) + 8 * y * z / (y + z) ^ 2 := by
  have hsum : 0 < y + z := add_pos hy hz
  have hid : (z + x) / y + (x + y) / z -
      (4 * x / (y + z) + 8 * y * z / (y + z) ^ 2) =
      (y - z) ^ 2 * (x * (y + z) + y ^ 2 + 4 * y * z + z ^ 2) /
        (y * z * (y + z) ^ 2) := by
    field_simp
    <;> ring
  have hnonneg : 0 ≤
      (y - z) ^ 2 * (x * (y + z) + y ^ 2 + 4 * y * z + z ^ 2) /
        (y * z * (y + z) ^ 2) := by positivity
  linarith only [hid, hnonneg]

#print axioms solution
