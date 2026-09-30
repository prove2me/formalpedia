-- Prove2me | solution 1 for lean_workbook_plus_135
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:30:51.909041+00:00
-- url     : https://prove2.me/submissions/4878d4c2-70a3-4df4-9eda-f77b07afbd0e

import Mathlib

theorem solution (a b c : ℝ) : (4 / 3 * a ^ 2 + 8 / 3 * b ^ 2 + 8 * a * c + 12 * c ^ 2) ≥ 0 := by
  nlinarith [sq_nonneg (a + 3 * c), sq_nonneg b]
