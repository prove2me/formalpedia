-- Prove2me | solution 1 for lean_workbook_plus_71767
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:56:27.970352+00:00
-- url     : https://prove2.me/submissions/cdd05b82-79b8-4400-a6dc-09e2fa0e6dcb

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ x : ℝ, x ∈ Set.Icc 0 1 → ∃ y : ℝ, y ∈ Set.Icc 0 1 ∧ y ^ 2 = x := by
  intro x hx
  refine ⟨Real.sqrt x, ⟨Real.sqrt_nonneg x, ?_⟩, Real.sq_sqrt hx.1⟩
  exact (Real.sqrt_le_one).2 hx.2
