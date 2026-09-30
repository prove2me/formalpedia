-- Prove2me | solution 2 for lean_workbook_plus_76609
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:27:36.731556+00:00
-- url     : https://prove2.me/submissions/ed234a68-56bc-457e-bb92-e2e727ec984b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a / (b + c) + 1 / 2) * (b / (c + a) + 1 / 2) * (c / (a + b) + 1 / 2) ≥ 1 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
