-- Prove2me | solution 1 for lean_workbook_plus_53613
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:46:16.189477+00:00
-- url     : https://prove2.me/submissions/10463e1c-9aa4-4d98-a11a-fa2728ce7c12

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : x ≥ -4) : (x + 4) ^ 2 + 40 ≥ 40 := by
  (intros; nlinarith [sq_nonneg (x)])
