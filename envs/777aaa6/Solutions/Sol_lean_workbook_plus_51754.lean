-- Prove2me | solution 1 for lean_workbook_plus_51754
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:05:44.933991+00:00
-- url     : https://prove2.me/submissions/e323f2c6-803b-4229-9353-606258b95e5d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 9 * (a ^ 3 + b ^ 3 + c ^ 3) + 48 * (a ^ 2 * (b + c) + b ^ 2 * (c + a) + c ^ 2 * (a + b)) ≥ 35 * (a * b + b * c + c * a) * (a + b + c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc])
