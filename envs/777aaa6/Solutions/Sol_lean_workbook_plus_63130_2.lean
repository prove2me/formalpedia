-- Prove2me | solution 2 for lean_workbook_plus_63130
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:23:39.872378+00:00
-- url     : https://prove2.me/submissions/e3262470-223e-46df-87f5-8ad7795952cd

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : x^3 - 13 * x^2 + 55 * x - 75 = 0 ↔ x = 3 ∨ x = 5 := by
  intros
  grind
