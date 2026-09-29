-- Prove2me | solution 1 for lean_workbook_plus_75195
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:53:04.185464+00:00
-- url     : https://prove2.me/submissions/3482705f-d7ff-4840-b3d5-ed2a3217e2eb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c = 1) : a^2 / (1 - a^2) + b^2 / (1 - b^2) + c^2 / (1 - c^2) ≥ 1 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
