-- Prove2me | solution 1 for lean_workbook_plus_58837
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:59:13.199573+00:00
-- url     : https://prove2.me/submissions/91612270-1e31-49aa-b3c9-83bc3b65d82b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (f : ℝ → ℝ) (hx: ∀ x, (f x)^2 = 4) : ∀ x, (f x = 2 ∨ f x = -2) := by
  intros
  grind
