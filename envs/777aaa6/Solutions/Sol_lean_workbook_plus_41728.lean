-- Prove2me | solution 1 for lean_workbook_plus_41728
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:16:32.563358+00:00
-- url     : https://prove2.me/submissions/415498e5-f245-475f-a0cc-4969f9af008c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) (h₁ : 0 < b ∧ b ≤ a ∧ a ≤ 2) (h₂ : a * b ^ 2 ≤ 2) : a + 2 * b ≤ 4 := by
  intros
  nlinarith [sq_nonneg (2*a-b), sq_nonneg (a-2*b), sq_nonneg (a+b)]
