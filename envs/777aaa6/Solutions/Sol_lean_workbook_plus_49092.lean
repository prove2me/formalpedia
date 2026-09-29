-- Prove2me | solution 1 for lean_workbook_plus_49092
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:22:06.048783+00:00
-- url     : https://prove2.me/submissions/722c3ef6-b22d-4157-9de9-f33eaec0e5a3

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (A : Set ℝ) : ∃ f : ℝ → ℝ, Continuous f ∧ ∀ a ∈ A, ∀ b, f (a + b) + f (a - b) = 2 * f a := by
  refine ⟨id, continuous_id, ?_⟩
  intro a ha b
  change (a + b) + (a - b) = 2 * a
  ring
