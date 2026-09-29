-- Prove2me | solution 1 for lean_workbook_plus_55363
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:05:01.217898+00:00
-- url     : https://prove2.me/submissions/ccdbf50a-0f4c-4f2c-bb82-4fe582888b37

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ a₁ a₂ a₃ b c d : ℝ, a₁^2 + a₂^2 + a₃^2 + b^2 + c^2 + d^2 ≥ 2 * (a₁ * a₃ + a₁ * a₂ - a₂ * a₃ + b * c + b * d - c * d) := by
  intro a₁ a₂ a₃ b c d
  nlinarith [sq_nonneg (a₁-a₂-a₃), sq_nonneg (b-c-d)]
