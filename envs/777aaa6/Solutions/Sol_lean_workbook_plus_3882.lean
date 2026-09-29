-- Prove2me | solution 1 for lean_workbook_plus_3882
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:08:37.051379+00:00
-- url     : https://prove2.me/submissions/1140dae0-1a3b-4803-a10c-5d7ce6cfd4e5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (hab : a + b + c = 2) :  (a - 1) * (b - 1) * (c - 1) * (1 - a * b * c) ≥ (2375 * a ^ 4 * b ^ 4 * c ^ 4) / 512 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
