-- Prove2me | solution 1 for lean_workbook_plus_9473
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:14.267711+00:00
-- url     : https://prove2.me/submissions/997ab984-48bc-4547-b2bf-11cd0de80634

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) (h₁ : x / y = 6.5 / 9.1) : y = 9.1 / 6.5 * x := by
  intros
  norm_num at * <;> first | omega | nlinarith | grind
