-- Prove2me | solution 1 for lean_workbook_plus_16938
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:43:12.937355+00:00
-- url     : https://prove2.me/submissions/a4c888f0-4fb4-4e83-bd26-889648fb1608

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a : ℝ) (h : a > 0) : a + a^3 ≥ 2 * a^2 := by
  intros
  have hpos_a : (0 : ℝ) ≤ a := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (a + a^3) - (2 * a^2) := by
    calc
      0 ≤ (1 : ℝ) * (a) * ((1 + ((-1) * a)))^2 := by positivity
      _ = (a + a^3) - (2 * a^2) := by ring
  exact sub_nonneg.mp h
