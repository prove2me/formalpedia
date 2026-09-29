-- Prove2me | solution 1 for lean_workbook_plus_69775
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:56:06.059858+00:00
-- url     : https://prove2.me/submissions/cb915d19-8579-4055-9087-2da3211f456a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution (x y z : ℝ) : |x| + |y| + |z| ≤ |x + y - z| + |y + z - x| + |z + x - y| := by
  have hx := abs_add_le (x + y - z) (z + x - y)
  have hy := abs_add_le (x + y - z) (y + z - x)
  have hz := abs_add_le (y + z - x) (z + x - y)
  rw [show (x + y - z) + (z + x - y) = 2 * x by ring, abs_mul] at hx
  rw [show (x + y - z) + (y + z - x) = 2 * y by ring, abs_mul] at hy
  rw [show (y + z - x) + (z + x - y) = 2 * z by ring, abs_mul] at hz
  norm_num at hx hy hz
  linarith
