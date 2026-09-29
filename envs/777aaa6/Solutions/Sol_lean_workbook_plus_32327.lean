-- Prove2me | solution 1 for lean_workbook_plus_32327
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:02:39.156338+00:00
-- url     : https://prove2.me/submissions/ccf1029a-a27f-4816-a306-8d9414fd7d6b

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (u v : ℝ × ℝ) : ‖u‖ + ‖v‖ ≥ ‖u + v‖ := by
  exact norm_add_le u v
