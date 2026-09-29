-- Prove2me | solution 1 for lean_workbook_plus_33872
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:15:43.185421+00:00
-- url     : https://prove2.me/submissions/d5d8332a-f47e-4448-a54d-a7b596567c12

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) :
  (a - b) ^ 4 + (b - c) ^ 4 + (c - a) ^ 4 + a * b * (a - b) ^ 2 + b * c * (b - c) ^ 2 + c * a * (c - a) ^ 2 ≥ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
