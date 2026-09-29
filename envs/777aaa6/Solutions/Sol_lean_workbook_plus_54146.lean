-- Prove2me | solution 1 for lean_workbook_plus_54146
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:09:39.67783+00:00
-- url     : https://prove2.me/submissions/d729312f-4e24-49b9-9d23-541fbe2f1b13

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ) (ha : 2 < a) (hb : 2 < b) (hc : 2 < c) : a + b + c < a * b * c := by
  have hp := mul_pos (show 0 < a-2 by linarith) (show 0 < b-2 by linarith)
  have hab : a+b < a*b := by nlinarith
  have hab4 : 4 < a*b := by linarith
  have hq := mul_pos (show 0 < a*b-1 by linarith) (show 0 < c-2 by linarith)
  nlinarith
