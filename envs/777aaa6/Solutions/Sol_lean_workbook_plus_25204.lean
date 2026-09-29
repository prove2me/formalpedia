-- Prove2me | solution 1 for lean_workbook_plus_25204
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:20:23.508968+00:00
-- url     : https://prove2.me/submissions/30dfee18-05cf-4a3e-a6be-5f0d56d0eb93

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c d : ℝ) : (a * b + c * d) ^ 2 - (b ^ 2 + d ^ 2) * (a ^ 2 + c ^ 2) ≤ 0 := by
  intros
  have h : (0 : ℝ) ≤ (0) - ((a * b + c * d) ^ 2 - (b ^ 2 + d ^ 2) * (a ^ 2 + c ^ 2)) := by
    calc
      0 ≤ (1 : ℝ) * (((b * c) + ((-1) * a * d)))^2 := by positivity
      _ = (0) - ((a * b + c * d) ^ 2 - (b ^ 2 + d ^ 2) * (a ^ 2 + c ^ 2)) := by ring
  exact sub_nonneg.mp h
