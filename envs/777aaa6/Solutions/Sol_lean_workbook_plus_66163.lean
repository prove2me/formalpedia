-- Prove2me | solution 1 for lean_workbook_plus_66163
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:31:53.047605+00:00
-- url     : https://prove2.me/submissions/8131dc8e-7fcc-4bb6-82a2-d67495183bc7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (c * (b - a) / a + a * (c - b) / b + b * (a - c) / c) ≥ 0 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
