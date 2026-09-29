-- Prove2me | solution 1 for lean_workbook_plus_6081
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:24:57.831197+00:00
-- url     : https://prove2.me/submissions/d4a1a2ec-c7a3-4a73-9909-684bacf262b6

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) : (x-2)*(x-4)*(x-6) = 0 ↔ x^3 - 12*x^2 + 44*x - 48 = 0 := by
  have h : (x-2)*(x-4)*(x-6) = x^3-12*x^2+44*x-48 := by ring
  rw [h]
