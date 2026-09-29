-- Prove2me | solution 1 for lean_workbook_plus_26678
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:25:22.177121+00:00
-- url     : https://prove2.me/submissions/8261eee8-0b5a-4638-918e-9c69f668fc46

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a1 a2 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) : (a1 + a2) / 2 ≥ Real.sqrt (a1 * a2) := by
  (intros; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ a1 * a2 by positivity), Real.sqrt_nonneg (a1 * a2), sq_nonneg (a1), sq_nonneg (a2), sq_nonneg (a1 - a2), sq_nonneg (a1 + a2), mul_pos ha1 ha2])
