-- Prove2me | solution 1 for lean_workbook_plus_69499
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:30:41.740283+00:00
-- url     : https://prove2.me/submissions/2e917686-d52f-47a1-8cdf-cad1604b4040

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ)
    (h₁ : a^2 + b^2 + c^2 = 1) :
  4 * (a^2 + b^2 + c^2)^2 ≥ 3 * (a^4 + b^4 + c^4 + 3 * (a^2 * b^2 + b^2 * c^2 + a^2 * c^2)) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
