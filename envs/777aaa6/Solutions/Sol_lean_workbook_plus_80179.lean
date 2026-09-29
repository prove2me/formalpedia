-- Prove2me | solution 1 for lean_workbook_plus_80179
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:00:35.469302+00:00
-- url     : https://prove2.me/submissions/568aa7a9-65ad-4aa0-89fa-1245e8046ed3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (b c : ℝ) (hb : 0 < b) (hc : 0 < c) : (b + c) / 2 ≥ Real.sqrt (b * c) := by
  (intros; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ b * c by positivity), Real.sqrt_nonneg (b * c), sq_nonneg (b), sq_nonneg (c), sq_nonneg (b - c), sq_nonneg (b + c), mul_pos hb hc])
