-- Prove2me | solution 1 for lean_workbook_plus_74141
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:24:31.837533+00:00
-- url     : https://prove2.me/submissions/ec04a0ba-955d-43cd-b158-e6234614fd24

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (x : ℝ) (hx : x < 0) :
    x ^ 2 + x + 1 / x + 1 / (x ^ 2) ≥ 0 := by
  have hne : x ≠ 0 := ne_of_lt hx
  have hq : 0 ≤ x ^ 2 - x + 1 := by nlinarith [sq_nonneg (2 * x - 1)]
  have hid : x ^ 2 + x + 1 / x + 1 / (x ^ 2) =
      (x + 1) ^ 2 * (x ^ 2 - x + 1) / x ^ 2 := by
    field_simp [hne] <;> ring
  rw [hid]
  exact div_nonneg (mul_nonneg (sq_nonneg _) hq) (sq_nonneg _)

#print axioms solution
