-- Prove2me | solution 1 for lean_workbook_plus_47985
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:18:05.731787+00:00
-- url     : https://prove2.me/submissions/bc6929b0-3da2-4cff-9e40-ebf55ca3e1cc

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (h : a + b + c = 0) :
  (a * b + b * c + c * a) ^ 2 = (1 / 4) * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by
  have hc : c = -a-b := by linarith
  rw [hc]
  ring
