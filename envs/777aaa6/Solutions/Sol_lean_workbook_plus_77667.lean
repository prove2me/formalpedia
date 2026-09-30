-- Prove2me | solution 1 for lean_workbook_plus_77667
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:12:45.707364+00:00
-- url     : https://prove2.me/submissions/a28cd857-a615-49e4-a700-889c4aba26db

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (x y z : ℝ) :
    x ^ 4 + y ^ 4 + z ^ 4 - x ^ 3 * y - x ^ 3 * z - y ^ 3 * z -
      y ^ 3 * x - z ^ 3 * x - z ^ 3 * y + x * y * z ^ 2 + x * y ^ 2 * z +
        x ^ 2 * y * z ≥ 0 := by
  have hid : x ^ 4 + y ^ 4 + z ^ 4 - x ^ 3 * y - x ^ 3 * z - y ^ 3 * z -
      y ^ 3 * x - z ^ 3 * x - z ^ 3 * y + x * y * z ^ 2 + x * y ^ 2 * z +
        x ^ 2 * y * z =
      (((x - y) * (x + y - z)) ^ 2 + ((y - z) * (y + z - x)) ^ 2 +
        ((z - x) * (z + x - y)) ^ 2) / 2 := by ring
  rw [hid]
  positivity

#print axioms solution
