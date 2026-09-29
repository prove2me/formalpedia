-- Prove2me | solution 1 for lean_workbook_plus_44876
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:55:07.70662+00:00
-- url     : https://prove2.me/submissions/a633f4c5-85ff-4f1f-ac6b-3984ccac5e83

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) (h₁ : x + y = 3) (h₂ : x ≥ 0 ∧ y ≥ 0) : x * y ^ 2 ≤ 4 := by
  intros
  nlinarith [sq_nonneg (2*x-y), sq_nonneg (x-2*y), sq_nonneg (x+y)]
