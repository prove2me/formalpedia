-- Prove2me | solution 1 for lean_workbook_plus_46536
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:15:00.742014+00:00
-- url     : https://prove2.me/submissions/9c21f2b6-aadc-49e8-85c2-38b0ac91b01b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : (a + b) ^ 2 ≥ 2 * a * b := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
