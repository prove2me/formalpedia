-- Prove2me | solution 1 for lean_workbook_plus_70834
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:08:16.036323+00:00
-- url     : https://prove2.me/submissions/cb1c6a61-c8eb-442e-8825-03cf89d07ece

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

private lemma reciprocal_comparison (S u : ℝ) (hS : 4 ≤ S) :
    1 / (S + u ^ 2 - u) ≤ 1 / (4 + u ^ 2 - u) := by
  have hd : 0 < 4 + u ^ 2 - u := by nlinarith [sq_nonneg (u - 1 / 2)]
  exact one_div_le_one_div_of_le hd (by linarith)

theorem solution (x y z t : ℝ) (h : x + y + z + t ≥ 4) :
    1 / (x + y + z + t ^ 2) + 1 / (x + y + z ^ 2 + t) +
      1 / (x + y ^ 2 + z + t) + 1 / (x ^ 2 + y + z + t) ≤
      1 / (4 + t ^ 2 - t) + 1 / (4 - z + z ^ 2) +
        1 / (4 - y + y ^ 2) + 1 / (x ^ 2 + 4 - x) := by
  have ht : 1 / (x + y + z + t ^ 2) ≤ 1 / (4 + t ^ 2 - t) := by
    convert reciprocal_comparison (x+y+z+t) t h using 1 <;> ring
  have hz : 1 / (x + y + z ^ 2 + t) ≤ 1 / (4 - z + z ^ 2) := by
    convert reciprocal_comparison (x+y+z+t) z h using 1 <;> ring
  have hy : 1 / (x + y ^ 2 + z + t) ≤ 1 / (4 - y + y ^ 2) := by
    convert reciprocal_comparison (x+y+z+t) y h using 1 <;> ring
  have hx : 1 / (x ^ 2 + y + z + t) ≤ 1 / (x ^ 2 + 4 - x) := by
    convert reciprocal_comparison (x+y+z+t) x h using 1 <;> ring
  linarith

#print axioms solution
