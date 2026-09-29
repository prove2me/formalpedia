-- Prove2me | solution 1 for lean_workbook_plus_59795
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:04:08.686447+00:00
-- url     : https://prove2.me/submissions/4fe3c005-045f-4f8a-ada8-ca36b5522545

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (b : ℝ) : Real.sqrt ((b^2 + 4)/2) ≥ (b + 2)/2 := by
  apply Real.le_sqrt_of_sq_le
  nlinarith only [sq_nonneg (b-2)]
