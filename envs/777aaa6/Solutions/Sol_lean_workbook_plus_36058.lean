-- Prove2me | solution 1 for lean_workbook_plus_36058
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:37:49.421002+00:00
-- url     : https://prove2.me/submissions/64e59028-65a2-4288-9a9d-372011cc03a1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x : ℝ) : |(x^3 - x^2) / (x^4 + x^2 + 1)| ≤ 1 := by
  have hp : (0:ℝ) < x^4+x^2+1 := by positivity
  rw [abs_le]
  constructor
  · apply (le_div_iff₀ hp).mpr
    nlinarith [sq_nonneg (x^2-1), sq_nonneg (x^2+x), sq_nonneg (x+1)]
  · apply (div_le_iff₀ hp).mpr
    nlinarith [sq_nonneg (x^2-x), sq_nonneg x]
