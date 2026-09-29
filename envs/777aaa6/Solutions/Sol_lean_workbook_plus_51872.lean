-- Prove2me | solution 1 for lean_workbook_plus_51872
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:24:49.305483+00:00
-- url     : https://prove2.me/submissions/85fd2cb4-9d10-48fb-b2cb-55384e4b31e2

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c d : ℝ) (P : ℝ → ℝ) (hP : P = fun x : ℝ => x^4 + a*x^3 + b*x^2 + c*x + d) : P 1 = 827 ∧ P 2 = 1654 ∧ P 3 = 2481 → P 9 + P (-5) = 8012 := by
  intros
  grind
