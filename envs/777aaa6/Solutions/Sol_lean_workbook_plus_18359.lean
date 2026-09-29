-- Prove2me | solution 1 for lean_workbook_plus_18359
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:32:49.260104+00:00
-- url     : https://prove2.me/submissions/8e75c6ab-4c70-42da-9489-1bb4b15e1847

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (f g h : ℝ → ℝ) (f_def : ∀ x, f x = 2 * x - 3) (g_def : ∀ x, g x = 1 / 2 * x^2 - x) (h_def : ∀ x, h x = x^2 + 2) : ∀ x, f (g (h x)) = x^4 + 2 * x^2 - 3 := by
  intros
  grind
