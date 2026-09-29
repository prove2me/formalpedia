-- Prove2me | solution 1 for lean_workbook_plus_76181
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:18:55.182167+00:00
-- url     : https://prove2.me/submissions/e3365150-36d1-4842-8478-20c746dd5a1b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : a + b + c ≥ a - b / (b + 2) + b - c / (c + 2) + c - a / (a + 2) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc])
