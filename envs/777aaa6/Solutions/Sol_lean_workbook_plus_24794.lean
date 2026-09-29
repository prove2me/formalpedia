-- Prove2me | solution 1 for lean_workbook_plus_24794
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:52:26.053362+00:00
-- url     : https://prove2.me/submissions/4102ba2e-f299-4416-9bbf-635a8a9d64f0

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∃ u v : ℤ, u^2 - 30 * v^2 = 1 := by
  intros
  refine ⟨1, ?_⟩ <;> norm_num at *
