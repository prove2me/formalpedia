-- Prove2me | solution 1 for lean_workbook_plus_16687
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:17:01.763988+00:00
-- url     : https://prove2.me/submissions/1cee3ecb-c6d8-40ea-9195-3ee4fcd48a63

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a ∈ Set.Icc (0:ℝ) 1, 32*a^5 + 32*a^4 - 16*a^3 - 16*a^2 + 9*a - 1 ≥ 0) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
