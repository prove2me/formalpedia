-- Prove2me | solution 1 for lean_workbook_plus_55728
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:21:49.027798+00:00
-- url     : https://prove2.me/submissions/1e97b712-2ec0-4e1a-9434-cc206c962a57

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)(habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + 3 = 2 * (a * b + b * c + c * a)) : a^2 + 2 * b * c ≥ 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
