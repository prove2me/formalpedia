-- Prove2me | solution 1 for lean_workbook_plus_40167
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:25:56.407884+00:00
-- url     : https://prove2.me/submissions/871018ed-1543-410b-ab67-36b31a6f666d

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) : (a^2 + b^2)^2 ≥ (a + b + c) * (a + b - c) * (b + c - a) * (c + a - b) := by
  nlinarith [sq_nonneg (a^2+b^2-c^2),sq_nonneg (a^2-b^2)]
