-- Prove2me | solution 1 for lean_workbook_plus_50974
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:48:20.015692+00:00
-- url     : https://prove2.me/submissions/331c23dd-c5f3-4b54-a090-f8134ff44f7b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (w : ℝ) (h : w ≥ 3) : w * (w - 1) * (w - 3) ≥ 0 := by
  exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
