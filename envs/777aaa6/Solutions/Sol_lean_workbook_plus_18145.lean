-- Prove2me | solution 1 for lean_workbook_plus_18145
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:09:03.610761+00:00
-- url     : https://prove2.me/submissions/71b925df-655f-432b-b891-63f9f577f699

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) : (a^2 + b^2) * (1 / a^2 + 1 / b^2) + 4 ≥ 2 * (a + b) * (1 / a + 1 / b) := by
  rw [ge_iff_le, ← sub_nonneg]
  have key : (a^2 + b^2) * (1 / a^2 + 1 / b^2) + 4 - 2 * (a + b) * (1 / a + 1 / b)
      = (a^2 + b^2) * (a - b)^2 / (a^2 * b^2) := by
    field_simp
    ring
  rw [key]
  positivity
