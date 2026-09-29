-- Prove2me | solution 1 for lean_workbook_plus_16690
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:38:28.625997+00:00
-- url     : https://prove2.me/submissions/b62b4eba-90e5-4600-a0d7-26c501454276

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : (-44 / Real.sqrt 3 + 1) > -25 := by
  have hp : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hl : (44/26 : ℝ) < Real.sqrt 3 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hd : (44 : ℝ)/Real.sqrt 3 < 26 := (div_lt_iff₀ hp).2 (by linarith)
  rw [neg_div]
  linarith
