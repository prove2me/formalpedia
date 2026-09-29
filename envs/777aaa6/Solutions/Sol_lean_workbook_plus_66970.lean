-- Prove2me | solution 1 for lean_workbook_plus_66970
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:14:29.658434+00:00
-- url     : https://prove2.me/submissions/2f99f64d-d258-4b91-bfff-1769d96c686e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 8 * (a^3 + b^3 + c^3) ≥ 3 * (a + b) * (b + c) * (c + a) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
