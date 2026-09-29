-- Prove2me | solution 1 for lean_workbook_plus_4532
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:46:02.278838+00:00
-- url     : https://prove2.me/submissions/97d4a4df-05d3-426e-b97a-a6635f906bd9

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c d : ℝ) (p : ℝ → ℝ) (h₁ : p = fun x => x^4 + a*x^3 + b*x^2 + c*x + d) : p 1 = 10 ∧ p 2 = 20 ∧ p 3 = 30 → (p 12 + p (-8)) / 10 = 1984 := by
  intros
  grind
