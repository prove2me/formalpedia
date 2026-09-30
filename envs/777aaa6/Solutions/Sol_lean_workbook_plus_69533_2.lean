-- Prove2me | solution 2 for lean_workbook_plus_69533
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:30:36.297738+00:00
-- url     : https://prove2.me/submissions/162e0f97-528a-4022-8231-8123b162121b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^4 + b^4 + c^4 + a^2 * b^2 + a^2 * c^2 + b^2 * c^2 ≥ a^3 * b + b^3 * a + a^3 * c + c^3 * a + b^3 * c + c^3 * b := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
