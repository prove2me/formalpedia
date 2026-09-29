-- Prove2me | solution 1 for lean_workbook_plus_52723
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:18:36.36542+00:00
-- url     : https://prove2.me/submissions/d3753501-8431-4271-a088-b170017c8743

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution {a b c d : ℝ} : (a^2 + b^2 + c^2 + d^2)^2 ≥ 16 * a * b * c * d := by
  intros
  have h : (0 : ℝ) ≤ ((a^2 + b^2 + c^2 + d^2)^2) - (16 * a * b * c * d) := by
    calc
      0 ≤ (1 : ℝ) * (((d ^ 2) + ((-1) * (b ^ 2))))^2 + (2 : ℝ) * (((c * d) + ((-1) * a * b)))^2 + (1 : ℝ) * (((c ^ 2) + ((-1) * (a ^ 2))))^2 + (4 : ℝ) * (((b * d) + ((-1) * a * c)))^2 + (2 : ℝ) * (((b * c) + ((-1) * a * d)))^2 := by positivity
      _ = ((a^2 + b^2 + c^2 + d^2)^2) - (16 * a * b * c * d) := by ring
  exact sub_nonneg.mp h
