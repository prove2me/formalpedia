-- Prove2me | solution 2 for lean_workbook_plus_59684
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:33:55.555742+00:00
-- url     : https://prove2.me/submissions/d04c00d2-f0a1-4a94-b619-68505b30dfaf

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : a ≤ b) (hc : b ≤ c) : (a + b + 2) * (b + c + 4) * (c + a + 6) ≥ 8 * (a + 1) * (b + 2) * (c + 3) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
