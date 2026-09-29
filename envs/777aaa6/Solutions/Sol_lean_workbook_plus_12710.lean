-- Prove2me | solution 1 for lean_workbook_plus_12710
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:32:33.396272+00:00
-- url     : https://prove2.me/submissions/8ca8832d-4161-4ec7-8184-e31b8703e48c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b^2 - b*c + c^2)*(b - c)^2 + (c^2 - c*a + a^2)*(c - a)^2 + (a^2 - a*b + b^2)*(a - b)^2 ≥ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
