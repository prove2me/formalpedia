-- Prove2me | solution 1 for lean_workbook_plus_40716
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:40:18.844952+00:00
-- url     : https://prove2.me/submissions/f6372c0b-f278-459e-b745-cb13b13d0162

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) :
  2 * a^2 + 2 * b^2 ≥ 4 * a * b := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
