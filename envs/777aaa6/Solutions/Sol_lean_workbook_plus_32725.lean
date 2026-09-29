-- Prove2me | solution 1 for lean_workbook_plus_32725
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:27:04.25761+00:00
-- url     : https://prove2.me/submissions/d34f4d88-d866-49d9-a2e9-ae910f20f360

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c d : ℝ) (P : ℝ → ℝ) (hP : P = fun x : ℝ => x^4 + a*x^3 + b*x^2 + c*x + d) : P 1 = 10 ∧ P 2 = 20 ∧ P 3 = 30 → P 10 + P (-6) = 8104 := by
  intros
  grind
