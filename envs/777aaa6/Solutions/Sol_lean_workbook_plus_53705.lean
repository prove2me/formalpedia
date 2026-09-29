-- Prove2me | solution 1 for lean_workbook_plus_53705
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:41:44.074365+00:00
-- url     : https://prove2.me/submissions/70a6c2cb-9ab2-454f-80af-c3508802efd1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ a b c : ℝ, a^2 + b^2 + c^2 ≥ (1/3)*(a + b + c)^2 := by
  intro a b c
  intros
  have h : (0 : ℝ) ≤ (a^2 + b^2 + c^2) - ((1/3)*(a + b + c)^2) := by
    calc
      0 ≤ ((1 / 3) : ℝ) * ((c + ((-1) * b)))^2 + ((1 / 3) : ℝ) * ((c + ((-1) * a)))^2 + ((1 / 3) : ℝ) * ((b + ((-1) * a)))^2 := by positivity
      _ = (a^2 + b^2 + c^2) - ((1/3)*(a + b + c)^2) := by ring
  exact sub_nonneg.mp h
