-- Prove2me | solution 1 for lean_workbook_plus_78617
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:22:32.284099+00:00
-- url     : https://prove2.me/submissions/b8d6731b-a709-4400-af6f-f93dcf3b510d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (f : ℝ → ℝ) (h₁ : ∀ x, f x = 2 * x + 1) : f 3 = 7 := by
  intros
  grind
