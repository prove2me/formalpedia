-- Prove2me | solution 1 for lean_workbook_plus_10801
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:42:30.561332+00:00
-- url     : https://prove2.me/submissions/52726d73-8ab7-4582-9301-4981d7202885

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c d : ℝ) : a + b + c + d - a ^ 2 - b ^ 2 - c ^ 2 - d ^ 2 ≤ 1 := by
  intros
  have h : (0 : ℝ) ≤ (1) - (a + b + c + d - a ^ 2 - b ^ 2 - c ^ 2 - d ^ 2) := by
    calc
      0 ≤ ((1 / 4) : ℝ) * ((1 + ((-2) * d)))^2 + ((1 / 4) : ℝ) * ((1 + ((-2) * c)))^2 + ((1 / 4) : ℝ) * ((1 + ((-2) * b)))^2 + ((1 / 4) : ℝ) * ((1 + ((-2) * a)))^2 := by positivity
      _ = (1) - (a + b + c + d - a ^ 2 - b ^ 2 - c ^ 2 - d ^ 2) := by ring
  exact sub_nonneg.mp h
