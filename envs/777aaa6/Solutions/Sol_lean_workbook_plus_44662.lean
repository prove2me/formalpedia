-- Prove2me | solution 1 for lean_workbook_plus_44662
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:52:43.039518+00:00
-- url     : https://prove2.me/submissions/e0410b15-f37c-42be-acaf-71ceae214251

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (f : ℝ → ℝ) (f_def : ∀ x, f x = x^2 + 2*x + 1) : f 2 = 9 := by
  intros
  grind
