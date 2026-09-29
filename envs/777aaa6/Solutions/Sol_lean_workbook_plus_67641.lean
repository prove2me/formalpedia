-- Prove2me | solution 1 for lean_workbook_plus_67641
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:36:17.496511+00:00
-- url     : https://prove2.me/submissions/d2d6344e-7f92-4281-8651-45f0c518a2fd

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (f : ℝ → ℝ) (f_def : ∀ x, f x = x^3 + 7 * x^2 + 9 * x + 10) : f 2 = 64 ∧ f 3 = 127 := by
  intros
  grind
