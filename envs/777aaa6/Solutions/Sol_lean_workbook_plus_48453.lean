-- Prove2me | solution 1 for lean_workbook_plus_48453
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:37:57.297448+00:00
-- url     : https://prove2.me/submissions/687fc1fb-2f7a-4bea-bcc0-d99bc84ac57a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) :
  a^3 / (1 - b * c) + b^3 / (1 - c * a) + c^3 / (1 - a * b) ≤
    (a^4 + b^4 + c^4) / (2 * a * b * c * (a * b + b * c + c * a)) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
