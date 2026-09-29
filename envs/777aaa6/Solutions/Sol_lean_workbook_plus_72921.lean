-- Prove2me | solution 1 for lean_workbook_plus_72921
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:21:30.692114+00:00
-- url     : https://prove2.me/submissions/ac3728f1-8d6d-485d-9a84-b1fcd5504c11

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : (a * b + 1) / (a * b * (a^2 + a * b + b^2)) + (b * c + 1) / (b * c * (b^2 + b * c + c^2)) + (c * a + 1) / (c * a * (c^2 + c * a + a^2)) ≥ 12 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
