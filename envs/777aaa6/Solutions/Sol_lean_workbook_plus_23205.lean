-- Prove2me | solution 1 for lean_workbook_plus_23205
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:58:57.748629+00:00
-- url     : https://prove2.me/submissions/a8e1cbaa-9483-4c12-a6b5-cfd2919e5570

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (r : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = x^2 - 2)
  (h₁ : f r = r) :
  (r - 2) * (r + 1) = 0 := by
  intros
  grind
