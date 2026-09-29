-- Prove2me | solution 1 for lean_workbook_plus_49848
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:38:24.800094+00:00
-- url     : https://prove2.me/submissions/7ddc1d75-401e-4bd3-9a60-4ae422e034ee

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (f : ℝ → ℝ) (hf : ∀ x, ‖f x‖ ≤ x^2) : f 0 = 0 := by
  have h := hf 0
  norm_num at h
  exact h
