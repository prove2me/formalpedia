-- Prove2me | solution 1 for lean_workbook_plus_48985
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:26.224869+00:00
-- url     : https://prove2.me/submissions/a713f7be-ad1a-4b2c-9e4f-2c7d14c6e5e4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (p : ℝ) : p^2 - 6 * p = 0 ↔ p = 0 ∨ p = 6 := by
  intros
  norm_num at * <;> first | omega | nlinarith | grind
