-- Prove2me | solution 2 for lean_workbook_plus_66878
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:34:39.182704+00:00
-- url     : https://prove2.me/submissions/fa4d0954-8775-424d-bc01-b0612951a9d2

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) (hx : x > 0) : x^2 + 1 / (4 * x) ≥ 3 / 4 := by
  have hx' : x ≠ 0 := ne_of_gt hx
  rw [ge_iff_le, ← sub_nonneg]
  have : x^2 + 1 / (4 * x) - 3 / 4 = (x + 1) * (2 * x - 1)^2 / (4 * x) := by
    field_simp; ring
  rw [this]; positivity
