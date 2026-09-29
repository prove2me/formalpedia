-- Prove2me | solution 1 for lean_workbook_plus_58145
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:45:23.654433+00:00
-- url     : https://prove2.me/submissions/971ef651-8dec-4fc2-bb9f-9972f038fb86

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (c d : ℝ) : 6 * (c^2 + d^2) + 13 * c * d ≤ (25/4) * (c + d)^2 := by
  (intros; nlinarith [sq_nonneg (c), sq_nonneg (d), sq_nonneg (c - d), sq_nonneg (c + d)])
