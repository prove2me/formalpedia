-- Prove2me | solution 1 for lean_workbook_plus_22774
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:21:18.046122+00:00
-- url     : https://prove2.me/submissions/8758278d-b9fa-4048-b377-49e1f62de75b

import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b : ℝ) : (a > 0 ∧ b > 0) ∨ (a < 0 ∧ b < 0) → a * b > 0 := by
  intro h
  exact mul_pos_iff.mpr h
