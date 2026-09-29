-- Prove2me | solution 1 for lean_workbook_plus_15642
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:46:49.780047+00:00
-- url     : https://prove2.me/submissions/08df6da2-ec55-4b19-8bff-44c7643e66f4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (q e : ℝ)
  (h₀ : q = 18)
  (h₁ : e = 0) :
  abs ((-1)^5 * (q / 2) - (-1)^2 * (e / 2)) = 9 := by
  intros
  grind
