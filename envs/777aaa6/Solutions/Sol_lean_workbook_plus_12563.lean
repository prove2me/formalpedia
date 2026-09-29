-- Prove2me | solution 1 for lean_workbook_plus_12563
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:32:02.680444+00:00
-- url     : https://prove2.me/submissions/0a82ad04-591a-4876-b0b4-c09ddb9c3a66

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ)
  (h₀ : 0 ≤ x)
  (h₁ : x ≤ 1) :
  0 ≤ (1 - x) * x ∧ (1 - x) * x ≤ 1 / 4 := by
  constructor
  · exact mul_nonneg (sub_nonneg.mpr h₁) h₀
  · nlinarith [sq_nonneg (x-1/2)]
