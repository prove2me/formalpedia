-- Prove2me | solution 1 for lean_workbook_plus_35006
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:44:12.041582+00:00
-- url     : https://prove2.me/submissions/215b31cc-b5c9-481c-8879-91f323a81bb9

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) : a^2 * (1 + b^4) ≤ (a^4 + 1) / 2 * (1 + b^4) := by
  intros
  have h : (0 : ℝ) ≤ ((a^4 + 1) / 2 * (1 + b^4)) - (a^2 * (1 + b^4)) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * ((1 + ((-1) * (a ^ 2))))^2 + ((1 / 2) : ℝ) * (((b ^ 2) + ((-1) * (a ^ 2) * (b ^ 2))))^2 := by positivity
      _ = ((a^4 + 1) / 2 * (1 + b^4)) - (a^2 * (1 + b^4)) := by ring
  exact sub_nonneg.mp h
