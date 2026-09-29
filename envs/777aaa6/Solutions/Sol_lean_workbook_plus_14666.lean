-- Prove2me | solution 1 for lean_workbook_plus_14666
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:40:14.458611+00:00
-- url     : https://prove2.me/submissions/cd431f2c-1f0d-4fab-8986-eef7cadad8cd

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a * b * c * (a ^ 2 + b ^ 2 + c ^ 2) ≤ (a + b + c) ^ 5 / 81) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
