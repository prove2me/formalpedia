-- Prove2me | solution 1 for lean_workbook_plus_10625
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:27:23.736586+00:00
-- url     : https://prove2.me/submissions/22912c5c-1436-43a4-bf56-626ef3f94644

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b : ℝ) (h : |a| ≤ b) : -b ≤ a ∧ a ≤ b := by
  exact abs_le.mp h
