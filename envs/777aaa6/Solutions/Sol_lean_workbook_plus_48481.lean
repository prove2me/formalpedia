-- Prove2me | solution 1 for lean_workbook_plus_48481
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:41:27.245295+00:00
-- url     : https://prove2.me/submissions/761ddb31-8565-4095-9638-c33061d33674

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c d : ℝ) (p : ℝ → ℝ) (hp : p = fun x : ℝ => x^4 + a*x^3 + b*x^2 + c*x + d) : p 1 = 1993 ∧ p 2 = 3986 ∧ p 3 = 5979 → 1/4 * (p 11 + p (-7)) = 5233 := by
  intros
  grind
