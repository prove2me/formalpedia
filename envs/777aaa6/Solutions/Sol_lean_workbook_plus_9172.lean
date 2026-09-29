-- Prove2me | solution 1 for lean_workbook_plus_9172
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:37:39.198571+00:00
-- url     : https://prove2.me/submissions/cfb4160c-63a7-4655-b1a3-d55e735c45ae

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution {a b c : ℝ} : (1^2 + 1^2 + 1^2) * (a^2 + b^2 + c^2) ≥ (a + b + c)^2 := by
  intros
  have h : (0 : ℝ) ≤ ((1^2 + 1^2 + 1^2) * (a^2 + b^2 + c^2)) - ((a + b + c)^2) := by
    calc
      0 ≤ (1 : ℝ) * ((c + ((-1) * b)))^2 + (1 : ℝ) * ((c + ((-1) * a)))^2 + (1 : ℝ) * ((b + ((-1) * a)))^2 := by positivity
      _ = ((1^2 + 1^2 + 1^2) * (a^2 + b^2 + c^2)) - ((a + b + c)^2) := by ring
  exact sub_nonneg.mp h
