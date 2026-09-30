-- Prove2me | solution 1 for lean_workbook_plus_61729
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:13:34.185526+00:00
-- url     : https://prove2.me/submissions/4f52806d-ce39-4ea2-90ea-ae37396003fa

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : (a^2 + b^2) * (1 / a^2 + 1 / b^2) + 4 ≥ 2 * (a + b) * (1 / a + 1 / b) := by
  rw [ge_iff_le, ← sub_nonneg]
  have : (a^2 + b^2) * (1 / a^2 + 1 / b^2) + 4 - 2 * (a + b) * (1 / a + 1 / b)
      = (a^2 + b^2) * (a - b)^2 / (a^2 * b^2) := by
    field_simp
    ring
  rw [this]
  positivity
