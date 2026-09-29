-- Prove2me | solution 1 for lean_workbook_plus_61761
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:19:45.910215+00:00
-- url     : https://prove2.me/submissions/81c61a29-9787-4b74-b83e-392c4bb2c3cb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a^3 + b^3 = a - b) : a^2 + b^2 < 1 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
