-- Prove2me | solution 1 for lean_workbook_plus_44396
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:36:23.548529+00:00
-- url     : https://prove2.me/submissions/7278ecf8-fb99-404e-b9bc-cef96a03eff0

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (f : ℝ → ℝ)
  (h₀ : ∀ x, (x = 0 ∨ f x * (f x - x) = 0)) :
  ∀ x, (x = 0 ∨ f x = 0) ∨ f x = x := by
  intros
  grind
