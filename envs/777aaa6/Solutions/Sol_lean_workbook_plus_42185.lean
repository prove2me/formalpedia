-- Prove2me | solution 1 for lean_workbook_plus_42185
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:27:38.964347+00:00
-- url     : https://prove2.me/submissions/4ecdb5c9-c4b8-499a-99c2-14c6683c57dc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : 2 * (a^4 + b^4) ≥ 2 * (a * b^3 + b * a^3) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
