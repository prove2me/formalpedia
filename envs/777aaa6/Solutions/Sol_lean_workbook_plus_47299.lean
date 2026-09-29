-- Prove2me | solution 1 for lean_workbook_plus_47299
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:29.877919+00:00
-- url     : https://prove2.me/submissions/394e08a7-ce5e-4a3c-b32f-20f2a79999e9

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : (2:ℝ) ^ 845 > 3 ^ 362 := by
  intros
  norm_num at * <;> first | omega | nlinarith | grind
