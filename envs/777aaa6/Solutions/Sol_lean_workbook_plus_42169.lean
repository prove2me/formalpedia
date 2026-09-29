-- Prove2me | solution 1 for lean_workbook_plus_42169
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:11:46.567718+00:00
-- url     : https://prove2.me/submissions/fdf5ca13-58cc-4183-8ec8-8227154ea0db

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a ∈ Set.Icc 1 2 ∧ b ∈ Set.Icc 1 2 ∧ c ∈ Set.Icc 1 2 → (a + 5 * b + 9 * c) * (1 / a + 5 / b + 9 / c) ≤ 225) := by
  push_neg
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
