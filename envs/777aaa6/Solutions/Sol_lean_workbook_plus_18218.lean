-- Prove2me | solution 1 for lean_workbook_plus_18218
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:20:18.880124+00:00
-- url     : https://prove2.me/submissions/7b96f2a3-9d6e-4234-9f77-1c879c171aad

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c d : ℝ) : (a^2+c^2)*(b^2+d^2)*(c^2+d^2+a^2+b^2) ≥ (a*b*c+b*c*d+c*d*a+d*a*b)^2 := by
  intros
  have h : (0 : ℝ) ≤ ((a^2+c^2)*(b^2+d^2)*(c^2+d^2+a^2+b^2)) - ((a*b*c+b*c*d+c*d*a+d*a*b)^2) := by
    calc
      0 ≤ (1 : ℝ) * (((c * (d ^ 2)) + ((-1) * a * (b ^ 2))))^2 + (1 : ℝ) * (((d * (c ^ 2)) + ((-1) * b * (a ^ 2))))^2 + (1 : ℝ) * (((b * c * d) + ((-1) * a * c * d)))^2 + (1 : ℝ) * (((b * (c ^ 2)) + ((-1) * a * b * d)))^2 + (1 : ℝ) * (((c * (b ^ 2)) + ((-1) * d * (a ^ 2))))^2 + (1 : ℝ) * (((a * (d ^ 2)) + ((-1) * a * b * c)))^2 := by positivity
      _ = ((a^2+c^2)*(b^2+d^2)*(c^2+d^2+a^2+b^2)) - ((a*b*c+b*c*d+c*d*a+d*a*b)^2) := by ring
  exact sub_nonneg.mp h
