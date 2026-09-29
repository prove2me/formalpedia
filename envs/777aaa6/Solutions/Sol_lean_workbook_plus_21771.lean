-- Prove2me | solution 1 for lean_workbook_plus_21771
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:31.979262+00:00
-- url     : https://prove2.me/submissions/d3dd7324-3554-4ca1-be95-e2c7243c9a87

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n : ℕ) (hn : n ≠ 0) : ((n:ℝ) / √(n * (n + 1)))^2 + (1 / √(n + 1))^2 = 1 := by
  intros
  norm_num at * <;> first | omega | nlinarith | grind
