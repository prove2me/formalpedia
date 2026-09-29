-- Prove2me | solution 1 for lean_workbook_plus_59083
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:27:45.374842+00:00
-- url     : https://prove2.me/submissions/88a43616-c4c1-4032-9113-e90e4e22ab66

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x1 x2 : ℝ)
  (h₀ : 0 < x1 ∧ 0 < x2)
  (h₁ : x1 > x2) :
  x1 - x2 + (1 / x1 - 1 / x2) = (x1 - x2) * (x1 * x2 - 1) / (x1 * x2) := by
  intros
  grind
