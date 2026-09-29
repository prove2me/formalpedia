-- Prove2me | solution 1 for lean_workbook_plus_57647
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:59:21.182347+00:00
-- url     : https://prove2.me/submissions/ff4625eb-eb96-4653-bf5d-5b103ad8fae1

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a - b) ^ 2 * (c / 2 - 1 / 2 - c / (a + b + Real.sqrt (2 * (a ^ 2 + b ^ 2)))) ≥ 0) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
