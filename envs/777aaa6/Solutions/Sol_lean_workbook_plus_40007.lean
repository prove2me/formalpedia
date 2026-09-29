-- Prove2me | solution 1 for lean_workbook_plus_40007
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:00:45.703919+00:00
-- url     : https://prove2.me/submissions/7355ffc2-fe5d-4510-aadd-c297a535f5a1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : abs x + x ^ 2 + abs (abs x - 1) + 6 * abs (x - 2) + abs (x ^ 2 - 1) + 3 * abs (2 * x + 1) ≥ 17 := by
  intros
  grind
