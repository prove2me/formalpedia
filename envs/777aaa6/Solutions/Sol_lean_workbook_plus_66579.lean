-- Prove2me | solution 1 for lean_workbook_plus_66579
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:48:00.401041+00:00
-- url     : https://prove2.me/submissions/20ae31aa-315b-4a11-96fe-36ecf7d2cdbd

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (hab : a * b + b * c + c * a = 1) : (a^2 + 2 * b * c) * (b^2 + 2 * c * a) * (c^2 + 2 * a * b) ≥ 1 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
