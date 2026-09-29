-- Prove2me | solution 1 for lean_workbook_plus_46818
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:39:16.120213+00:00
-- url     : https://prove2.me/submissions/e1c95bc7-4f85-4740-aee7-1f4417fcce61

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) (h₁ : x = Real.sqrt 5) (h₂ : y = Real.sqrt 7) : y = Real.sqrt (x^2 + 2) := by
  intros
  norm_num at * <;> first | omega | nlinarith | grind
