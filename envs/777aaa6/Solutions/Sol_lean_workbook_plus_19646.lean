-- Prove2me | solution 1 for lean_workbook_plus_19646
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:17:18.759654+00:00
-- url     : https://prove2.me/submissions/3dcd68c6-0aa3-410c-a64f-644701c030dc

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (1 + a ^ 2) * (1 + b ^ 2) ≥ a * (1 + b ^ 2) + b * (1 + a ^ 2) := by
  intros
  have h : (0 : ℝ) ≤ ((1 + a ^ 2) * (1 + b ^ 2)) - (a * (1 + b ^ 2) + b * (1 + a ^ 2)) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * ((1 + ((-1) * b)))^2 + ((1 / 2) : ℝ) * ((1 + ((-1) * a)))^2 + ((1 / 2) : ℝ) * ((b + ((-1) * a * b)))^2 + ((1 / 2) : ℝ) * ((a + ((-1) * a * b)))^2 := by positivity
      _ = ((1 + a ^ 2) * (1 + b ^ 2)) - (a * (1 + b ^ 2) + b * (1 + a ^ 2)) := by ring
  exact sub_nonneg.mp h
