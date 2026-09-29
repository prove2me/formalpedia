-- Prove2me | solution 1 for lean_workbook_plus_47123
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:37:08.704227+00:00
-- url     : https://prove2.me/submissions/55921a04-f438-47b2-a3da-e1e799e1a7ba

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a:ℝ) (ha : a ≥ 0) : a^6 + 2 ≥ a^3 + a^2 + a := by
  intros
  
  have h : (0 : ℝ) ≤ (a^6 + 2) - (a^3 + a^2 + a) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * (1) * ((1 + ((-1) * a)))^2 + (1 : ℝ) * (1) * ((1 + ((-1) * (a ^ 2))))^2 + ((1 / 2) : ℝ) * (1) * ((1 + ((-1) * (a ^ 3))))^2 + ((1 / 2) : ℝ) * (1) * ((a + ((-1) * (a ^ 3))))^2 := by positivity
      _ = (a^6 + 2) - (a^3 + a^2 + a) := by ring
  exact sub_nonneg.mp h
