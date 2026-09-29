-- Prove2me | solution 1 for lean_workbook_plus_13433
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:47:45.585454+00:00
-- url     : https://prove2.me/submissions/2ba7677b-f46b-4feb-bcb4-c3dda294da66

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : 50 * (2 * x + 1) > 99 * (x + 1) ↔ x > 49 := by
  intros
  grind
