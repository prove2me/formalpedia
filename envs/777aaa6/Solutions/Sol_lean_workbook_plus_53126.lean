-- Prove2me | solution 1 for lean_workbook_plus_53126
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:46:51.64435+00:00
-- url     : https://prove2.me/submissions/99efc913-1a43-4969-96e6-d1e22c0ecadc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) :
  1 ≤ a / (1 + b * c) + b / (1 + a * c) + c / (1 + a * b) ∧
    a / (1 + b * c) + b / (1 + a * c) + c / (1 + a * b) ≤ Real.sqrt 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
