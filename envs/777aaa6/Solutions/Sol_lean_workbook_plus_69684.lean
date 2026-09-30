-- Prove2me | solution 1 for lean_workbook_plus_69684
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:34:08.576864+00:00
-- url     : https://prove2.me/submissions/e4e2940c-36d0-4cfe-997c-a4c586de5896

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem solution (x y z a b c : ℝ) (h1 : x + y + z = 0) (h2 : a + b + c = 0) :
    4 * (a * x + b * y + c * z) ^ 3 -
      3 * (a * x + b * y + c * z) * (a ^ 2 + b ^ 2 + c ^ 2) *
        (x ^ 2 + y ^ 2 + z ^ 2) -
      2 * (b - c) * (c - a) * (a - b) * (y - z) * (z - x) * (x - y) =
      54 * a * b * c * x * y * z := by
  have hz : z = -x - y := by linarith
  have hc : c = -a - b := by linarith
  rw [hz, hc]
  ring

#print axioms solution
