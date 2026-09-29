-- Prove2me | solution 1 for lean_workbook_plus_27780
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:38:20.793627+00:00
-- url     : https://prove2.me/submissions/9a5bb123-793b-487e-abd6-85227d2eb009

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : (Real.sqrt 2 / 2) ≥ (1 / 3) / (Real.sqrt 2 / 3) := by
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  apply le_of_eq
  field_simp [ne_of_gt hp]
  <;> nlinarith only [hs]
