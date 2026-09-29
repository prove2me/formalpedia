-- Prove2me | solution 1 for lean_workbook_plus_66130
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:46:56.070272+00:00
-- url     : https://prove2.me/submissions/5c7af5bb-9e87-42e9-9239-1d7060061ed7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ a b : ℝ, a^2 + a * b + b^2 ≥ 3 * (a + b - 1) ∧ a^2 + a * b + b^2 ≥ 3 * a * b * (a + b - a * b) ∧ a^2 + a * b + b^2 ≤ 3 * (a^2 - a + 1) * (b^2 - b + 1) := by
  intro a b
  have hA : a^2+a*b+b^2 ≥ 3*(a+b-1) := by nlinarith only [sq_nonneg (a-b), sq_nonneg (a+b-2)]
  have hB : a^2+a*b+b^2 ≥ 3*a*b*(a+b-a*b) := by nlinarith only [sq_nonneg (a-b), sq_nonneg (a+b-2*a*b)]
  refine ⟨hA,hB,?_⟩
  nlinarith only [hA,hB]
