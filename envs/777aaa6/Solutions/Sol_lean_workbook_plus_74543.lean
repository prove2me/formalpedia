-- Prove2me | solution 1 for lean_workbook_plus_74543
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:52:17.109039+00:00
-- url     : https://prove2.me/submissions/a9bd70c3-8eda-4c78-86df-c97f89c9ef54

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a - b) * (2 * a + b) * (a ^ 2 + b ^ 2) + (b - c) * (2 * b + c) * (b ^ 2 + c ^ 2) + (c - a) * (2 * c + a) * (c ^ 2 + a ^ 2) ≥ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
