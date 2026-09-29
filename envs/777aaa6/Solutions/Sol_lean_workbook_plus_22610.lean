-- Prove2me | solution 1 for lean_workbook_plus_22610
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:37:16.78125+00:00
-- url     : https://prove2.me/submissions/98b44463-ae89-4a36-bde7-6cb3a6103f8b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a : ℝ) : (1 + a^2 + a^4)^2 ≥ (a + a^2 + a^3)^2 := by
  intros
  have h : (0 : ℝ) ≤ ((1 + a^2 + a^4)^2) - ((a + a^2 + a^3)^2) := by
    calc
      0 ≤ (1 : ℝ) * ((1 + ((-1) * (a ^ 3))))^2 + (1 : ℝ) * ((a + ((-1) * (a ^ 4))))^2 := by positivity
      _ = ((1 + a^2 + a^4)^2) - ((a + a^2 + a^3)^2) := by ring
  exact sub_nonneg.mp h
