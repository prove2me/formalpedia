-- Prove2me | solution 1 for lean_workbook_plus_12686
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:31:56.368682+00:00
-- url     : https://prove2.me/submissions/378ae3ba-5a89-422b-a437-ed05de09a057

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : a ^ 3 + b ^ 3 + c ^ 3 ≥ a ^ 2 * b + b ^ 2 * c + c ^ 2 * a := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc])
