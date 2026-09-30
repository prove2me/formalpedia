-- Prove2me | solution 2 for lean_workbook_plus_81130
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:51:16.825807+00:00
-- url     : https://prove2.me/submissions/87a900f7-431c-4ce3-8842-6673495421a0

import Mathlib

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (9 / 4 - (x / (x + y) + y / (y + z) + z / (z + x)) *
      (y / (x + y) + z / (y + z) + x / (z + x))) =
    (1 / 4) * ((y - z) ^ 2 * (x - z) ^ 2 * (x - y) ^ 2) /
      ((x + y) ^ 2 * (y + z) ^ 2 * (z + x) ^ 2) := by
  have hxy : x + y ≠ 0 := ne_of_gt (add_pos hx hy)
  have hyz : y + z ≠ 0 := ne_of_gt (add_pos hy hz)
  have hzx : z + x ≠ 0 := ne_of_gt (add_pos hz hx)
  field_simp
  ring
