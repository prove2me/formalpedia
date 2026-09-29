-- Prove2me | solution 1 for lean_workbook_plus_8603
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:36:24.312115+00:00
-- url     : https://prove2.me/submissions/5bef31d8-7514-492e-a878-323b9047052c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) (f : ℝ → ℝ) (h : ∀ x, f x = a * x ^ 2 + b * x + c) : ∀ x, f (x + 3) - 3 * f (x + 2) + 3 * f (x + 1) - f x = 0 := by
  intros
  grind
