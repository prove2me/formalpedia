-- Prove2me | solution 2 for lean_workbook_plus_47428
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:40:32.677693+00:00
-- url     : https://prove2.me/submissions/ab15d260-6f4e-4691-a089-850284244ab6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (hx : 0 < x) : 3*x^4 + 1 ≥ 4*x^3 := by
  intros
  
  have h : (0 : ℝ) ≤ (3*x^4 + 1) - (4*x^3) := by
    calc
      0 ≤ (1 : ℝ) * (1) * ((1 + ((-1) * (x ^ 2))))^2 + (2 : ℝ) * (1) * ((x + ((-1) * (x ^ 2))))^2 := by positivity
      _ = (3*x^4 + 1) - (4*x^3) := by ring
  exact sub_nonneg.mp h
