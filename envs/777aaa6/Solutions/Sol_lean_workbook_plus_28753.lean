-- Prove2me | solution 1 for lean_workbook_plus_28753
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:05:11.511913+00:00
-- url     : https://prove2.me/submissions/12a0c1d8-7a57-4a57-a1c6-fbf4beb0de77

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (habc : a + b * c = 2) : a ^ 2 + b ^ 2 + c ^ 2 + a * b * c ≥ 4 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
