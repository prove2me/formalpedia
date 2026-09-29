-- Prove2me | solution 1 for lean_workbook_plus_50454
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:50:25.878126+00:00
-- url     : https://prove2.me/submissions/1403476c-9786-42e7-8e5e-e97fc2bab8a2

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (f : ℝ → ℝ) (hf : ∀ x, f 0 = f (x^2 - f x) + 4 * (f x)^2) : ∀ x, f 0 - f (x^2 - f x) = 4 * (f x)^2 := by
  intros
  grind
