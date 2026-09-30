-- Prove2me | solution 2 for lean_workbook_plus_38227
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:52:31.950931+00:00
-- url     : https://prove2.me/submissions/e76d1cbf-2109-40dc-85a4-7208db745b77

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : a^4 + b^4 ≥ 2 * a^2 * b^2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
