-- Prove2me | solution 1 for lean_workbook_plus_13494
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:47:23.084005+00:00
-- url     : https://prove2.me/submissions/175ab6ba-5f1f-4f4f-a0e1-c81e78e4a9c3

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a : ℝ) (h : 2*a^2 - 3*a - 2 = 0) : a = 2 ∨ a = -1/2 := by
  intros
  grind
