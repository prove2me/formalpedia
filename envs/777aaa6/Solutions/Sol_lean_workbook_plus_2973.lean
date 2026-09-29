-- Prove2me | solution 1 for lean_workbook_plus_2973
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:15:17.332581+00:00
-- url     : https://prove2.me/submissions/613d1dbd-4fbb-464f-96a7-6c84cd6b515f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c: ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a^3 + b^3 + c^3 ≥ a^2 * b + b^2 * c + c^2 * a := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
