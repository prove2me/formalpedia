-- Prove2me | solution 1 for lean_workbook_plus_27772
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:58:28.364274+00:00
-- url     : https://prove2.me/submissions/2c047265-29de-4a60-b869-31fad6c08e05

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (t : ℝ) : (t < -3/2 ∨ 3/2 < t) → 0 < (t^2 - 9/4) := by
  rintro (h|h) <;> nlinarith only [h,sq_nonneg (t+3/2),sq_nonneg (t-3/2)]
