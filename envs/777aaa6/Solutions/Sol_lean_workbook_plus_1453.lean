-- Prove2me | solution 1 for lean_workbook_plus_1453
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:33:21.272385+00:00
-- url     : https://prove2.me/submissions/ebf6e3f4-cfd7-43a9-ac87-8f9b85fa143c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a * b * c + (13/3) * (a + b + c) ^ 3 ≥ (25/2) * (a + b) * (b + c) * (c + a) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
