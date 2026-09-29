-- Prove2me | solution 1 for lean_workbook_plus_40764
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:40:21.26066+00:00
-- url     : https://prove2.me/submissions/759678dc-a835-47c1-a96a-66ccbbaa60b9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (b c : ℝ) :
  32 * b^4 + 35 * b^2 * c^2 - 44 * b^3 * c - 18 * b * c^3 + 27 * c^4 ≥ 0 := by
  (intros; nlinarith [sq_nonneg (b), sq_nonneg (c), sq_nonneg (b - c), sq_nonneg (b + c)])
