-- Prove2me | solution 1 for lean_workbook_plus_17552
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:38:37.561428+00:00
-- url     : https://prove2.me/submissions/396db307-cb6e-48d8-81d0-d7dabe4d2caa

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) : a^2 * (1 + b^4) + b^2 * (1 + a^4) ≤ (1 + a^4) * (1 + b^4) := by
  intros
  have h : (0 : ℝ) ≤ ((1 + a^4) * (1 + b^4)) - (a^2 * (1 + b^4) + b^2 * (1 + a^4)) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * ((1 + ((-1) * (b ^ 2))))^2 + ((1 / 2) : ℝ) * ((1 + ((-1) * (a ^ 2))))^2 + ((1 / 2) : ℝ) * (((b ^ 2) + ((-1) * (a ^ 2) * (b ^ 2))))^2 + ((1 / 2) : ℝ) * (((a ^ 2) + ((-1) * (a ^ 2) * (b ^ 2))))^2 := by positivity
      _ = ((1 + a^4) * (1 + b^4)) - (a^2 * (1 + b^4) + b^2 * (1 + a^4)) := by ring
  exact sub_nonneg.mp h
