-- Prove2me | solution 1 for lean_workbook_plus_76835
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:26:39.012794+00:00
-- url     : https://prove2.me/submissions/b039d631-50e6-440e-ab25-461ca82b04ac

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 3 * (a^2 - a * b + b^2 - b * c + c^2 - c * a) ≥ (a + b + c)^2 - 3 * (a * b + b * c + c * a) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
