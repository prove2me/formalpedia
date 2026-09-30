-- Prove2me | solution 1 for lean_workbook_plus_75055
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:15:39.628626+00:00
-- url     : https://prove2.me/submissions/8cd10013-e756-4695-93a7-d303375e3380

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : 3 * (x + y) ≥ 2 * (x * y + 1)) :
    x ^ 2 + y ^ 2 ≥ 2 / 7 * (x ^ 2 * y ^ 2 + 1) := by
  have hm : 0 ≤ (3 * (x + y) - 2 * (x * y + 1)) *
      (3 * (x + y) + 2 * (x * y + 1)) :=
    mul_nonneg (sub_nonneg.mpr h) (by positivity)
  nlinarith [sq_nonneg (x - y)]

#print axioms solution
